/// <reference types="node" />

import { spawn } from "node:child_process";
import { mkdtemp, open, rm, stat, writeFile } from "node:fs/promises";
import { createServer, type Server } from "node:http";
import { tmpdir } from "node:os";
import { join } from "node:path";
import type { SatRequest, SatResult, SatSolver } from "./index.js";
import {
  DIMACS_CONTENT_TYPE,
  LRAT_CONTENT_TYPE,
  MODEL_CONTENT_TYPE,
} from "./sat-http.js";

export interface CadicalOptions {
  executable?: string;
  timeoutMs?: number;
  maxStdoutBytes?: number;
  maxStderrBytes?: number;
  maxProofBytes?: number;
  /** Debug-only human-readable proof output. Binary LRAT is the default. */
  asciiProof?: boolean;
}

const MAX_BUFFER_BYTES = 256 * 1024 * 1024;
const MAX_TIMEOUT_MS = 24 * 60 * 60 * 1000;
const MAX_MODEL_LITERALS = 10_000_000;

/** Runs an untrusted CaDiCaL executable with no shell and bounded resources. */
export class CadicalSolver implements SatSolver {
  readonly #options: Required<CadicalOptions>;

  constructor(options: CadicalOptions = {}) {
    this.#options = {
      executable: options.executable ?? "cadical",
      timeoutMs: options.timeoutMs ?? 30_000,
      maxStdoutBytes: options.maxStdoutBytes ?? 8 * 1024 * 1024,
      maxStderrBytes: options.maxStderrBytes ?? 1024 * 1024,
      maxProofBytes: options.maxProofBytes ?? 64 * 1024 * 1024,
      asciiProof: options.asciiProof ?? false,
    };
    boundedInteger(this.#options.timeoutMs, "timeout", MAX_TIMEOUT_MS, true);
    boundedInteger(this.#options.maxStdoutBytes, "stdout", MAX_BUFFER_BYTES);
    boundedInteger(this.#options.maxStderrBytes, "stderr", MAX_BUFFER_BYTES);
    boundedInteger(this.#options.maxProofBytes, "proof", MAX_BUFFER_BYTES);
  }

  async solve(request: SatRequest, signal?: AbortSignal): Promise<SatResult> {
    if (process.platform === "win32") {
      throw new Error(
        "the native CaDiCaL adapter requires POSIX process groups; use HttpSatSolver on Windows",
      );
    }
    boundedInteger(
      request.limits.maxModelLiterals,
      "model",
      MAX_MODEL_LITERALS,
    );
    boundedInteger(request.limits.maxProofBytes, "proof", MAX_BUFFER_BYTES);
    if (signal?.aborted) throw new Error("CaDiCaL solve aborted");
    const directory = await mkdtemp(join(tmpdir(), "nucleus-cadical-"));
    const input = join(directory, "input.cnf");
    const proof = join(directory, "proof.lrat");
    try {
      await writeFile(input, request.dimacs, { flag: "wx", mode: 0o600 });
      const args = [
        "--quiet",
        "--lrat",
        this.#options.asciiProof ? "--no-binary" : "--binary",
        input,
        proof,
      ];
      const run = await runBounded(
        this.#options.executable,
        args,
        proof,
        Math.min(request.limits.maxProofBytes, this.#options.maxProofBytes),
        this.#options,
        signal,
      );
      if (run.code !== 10 && run.code !== 20) {
        throw new Error(`CaDiCaL exited with status ${run.code}`);
      }
      const status = parseStatus(run.stdout, request.limits.maxModelLiterals);
      if (run.code === 10 && status.kind === "sat") return status;
      if (run.code === 20 && status.kind === "unsat") {
        return {
          kind: "unsat",
          proof: await readProofBounded(
            proof,
            Math.min(request.limits.maxProofBytes, this.#options.maxProofBytes),
          ),
        };
      }
      throw new Error(`CaDiCaL returned inconsistent exit status ${run.code}`);
    } finally {
      await rm(directory, { recursive: true, force: true });
    }
  }
}

async function readProofBounded(
  path: string,
  limit: number,
): Promise<Uint8Array> {
  if (!Number.isSafeInteger(limit) || limit < 0)
    throw new Error("invalid CaDiCaL proof bound");
  let file;
  try {
    file = await open(path, "r");
  } catch {
    throw new Error("CaDiCaL did not produce a readable LRAT proof");
  }
  await using _file = file;
  const output = new Uint8Array(limit + 1);
  let length = 0;
  for (;;) {
    const { bytesRead } = await file.read(
      output,
      length,
      output.length - length,
    );
    length += bytesRead;
    if (length > limit)
      throw new Error("CaDiCaL proof exceeds its response bound");
    if (bytesRead === 0) return output.slice(0, length);
  }
}

interface RunResult {
  code: number | null;
  stdout: Uint8Array;
}

async function runBounded(
  executable: string,
  args: string[],
  proof: string,
  maxProofBytes: number,
  options: Required<CadicalOptions>,
  signal?: AbortSignal,
): Promise<RunResult> {
  if (signal?.aborted) throw new Error("CaDiCaL solve aborted");
  const child = spawn(executable, args, {
    detached: true,
    shell: false,
    stdio: ["ignore", "pipe", "pipe"],
    windowsHide: true,
  });
  const stdout: Uint8Array[] = [];
  let stdoutBytes = 0;
  let stderrBytes = 0;
  let failure: Error | undefined;
  const killGroup = () => {
    if (child.pid !== undefined) {
      try {
        process.kill(-child.pid, "SIGKILL");
        return;
      } catch {
        // A failed spawn or already-reaped group falls back to the child API.
      }
    }
    child.kill("SIGKILL");
  };
  const fail = (error: Error) => {
    failure ??= error;
    killGroup();
  };
  child.stdout.on("data", (chunk: Buffer) => {
    stdoutBytes += chunk.byteLength;
    if (stdoutBytes > options.maxStdoutBytes)
      fail(new Error("CaDiCaL stdout exceeds its bound"));
    else stdout.push(chunk);
  });
  child.stderr.on("data", (chunk: Buffer) => {
    stderrBytes += chunk.byteLength;
    if (stderrBytes > options.maxStderrBytes)
      fail(new Error("CaDiCaL stderr exceeds its bound"));
  });

  const onAbort = () => fail(new Error("CaDiCaL solve aborted"));
  signal?.addEventListener("abort", onAbort, { once: true });
  if (signal?.aborted) onAbort();
  const timeout = setTimeout(
    () => fail(new Error("CaDiCaL solve timed out")),
    options.timeoutMs,
  );
  let proofWatch: ReturnType<typeof setTimeout> | undefined;
  let proofInspection = Promise.resolve();
  let watching = true;
  const inspectProof = async () => {
    try {
      if ((await stat(proof)).size > maxProofBytes)
        fail(new Error("CaDiCaL proof exceeds its response bound"));
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== "ENOENT")
        fail(new Error("could not inspect CaDiCaL proof"));
    }
  };
  const scheduleProofInspection = () => {
    proofWatch = setTimeout(() => {
      proofInspection = inspectProof().finally(() => {
        if (watching) scheduleProofInspection();
      });
    }, 10);
  };
  scheduleProofInspection();
  try {
    const closed = new Promise<void>((resolve) =>
      child.once("close", () => resolve()),
    );
    const code = await new Promise<number | null>((resolve) => {
      child.once("error", (error) => {
        fail(new Error(`could not start CaDiCaL: ${error.message}`));
        resolve(null);
      });
      child.once("exit", resolve);
    });
    // The direct solver may exit while a descendant still owns its pipes.
    // Kill the group before waiting for close so those pipes cannot pin us.
    killGroup();
    await closed;
    if (failure) throw failure;
    return { code, stdout: Buffer.concat(stdout, stdoutBytes) };
  } finally {
    clearTimeout(timeout);
    watching = false;
    clearTimeout(proofWatch);
    await proofInspection;
    signal?.removeEventListener("abort", onAbort);
    killGroup();
  }
}

function parseStatus(stdout: Uint8Array, maxModelLiterals: number): SatResult {
  const text = new TextDecoder("utf-8", { fatal: true }).decode(stdout);
  const lines = text.split(/\r?\n/);
  const statuses = lines.filter(
    (line) => line === "s SATISFIABLE" || line === "s UNSATISFIABLE",
  );
  if (statuses.length !== 1)
    throw new Error("CaDiCaL returned no unique status line");
  if (statuses[0] === "s UNSATISFIABLE")
    return { kind: "unsat", proof: new Uint8Array() };
  const model: bigint[] = [];
  let terminated = false;
  for (const line of lines) {
    if (
      line === "" ||
      line.startsWith("c ") ||
      line === "s SATISFIABLE" ||
      line === "s UNSATISFIABLE"
    )
      continue;
    if (!line.startsWith("v "))
      throw new Error("CaDiCaL returned malformed output");
    for (const word of line.slice(2).trim().split(/\s+/)) {
      if (!/^-?(?:0|[1-9][0-9]*)$/.test(word))
        throw new Error("CaDiCaL returned a malformed model");
      const literal = BigInt(word);
      if (literal === 0n) {
        if (terminated)
          throw new Error("CaDiCaL returned duplicate model terminators");
        terminated = true;
      } else {
        if (terminated)
          throw new Error("CaDiCaL returned data after model terminator");
        if (literal < -(1n << 63n) || literal >= 1n << 63n)
          throw new Error("CaDiCaL returned an out-of-range model literal");
        model.push(literal);
        if (model.length > maxModelLiterals)
          throw new Error("CaDiCaL model exceeds its response bound");
      }
    }
  }
  if (!terminated) throw new Error("CaDiCaL model has no terminator");
  return { kind: "sat", model };
}

export interface CadicalServerOptions {
  solver: SatSolver;
  maxDimacsBytes?: number;
  maxModelLiterals?: number;
  maxProofBytes?: number;
}

/** Creates an ordinary HTTP server for a supplied untrusted solver. */
export function createCadicalServer(options: CadicalServerOptions): Server {
  const maxDimacsBytes = options.maxDimacsBytes ?? 16 * 1024 * 1024;
  const maxModelLiterals = options.maxModelLiterals ?? 1_000_000;
  const maxProofBytes = options.maxProofBytes ?? 64 * 1024 * 1024;
  boundedInteger(maxDimacsBytes, "DIMACS", MAX_BUFFER_BYTES);
  boundedInteger(maxModelLiterals, "model", MAX_MODEL_LITERALS);
  boundedInteger(maxProofBytes, "proof", MAX_BUFFER_BYTES);
  return createServer(async (request, response) => {
    if (request.method !== "POST") {
      response.writeHead(405, { allow: "POST" }).end();
      return;
    }
    if (
      request.headers["content-type"]?.split(";", 1)[0] !== DIMACS_CONTENT_TYPE
    ) {
      response.writeHead(415).end();
      return;
    }
    const controller = new AbortController();
    request.once("aborted", () => controller.abort());
    response.once("close", () => {
      if (!response.writableEnded) controller.abort();
    });
    try {
      const chunks: Buffer[] = [];
      let size = 0;
      for await (const chunk of request) {
        size += chunk.length;
        if (size > maxDimacsBytes)
          throw new HttpError(413, "DIMACS exceeds server bound");
        chunks.push(chunk);
      }
      if (controller.signal.aborted) throw new Error("SAT request aborted");
      const result = await abortable(
        options.solver.solve(
          {
            dimacs: Uint8Array.from(Buffer.concat(chunks, size)),
            limits: { maxModelLiterals, maxProofBytes },
          },
          controller.signal,
        ),
        controller.signal,
      );
      if (result.kind === "unknown")
        throw new HttpError(503, result.reason ?? "unknown");
      if (result.kind === "sat") {
        const model = serializeModel(result.model, maxModelLiterals);
        response.writeHead(200, {
          "content-type": MODEL_CONTENT_TYPE,
          "content-length": Buffer.byteLength(model),
        });
        response.end(model);
      } else {
        if (result.kind !== "unsat")
          throw new HttpError(502, "solver returned an invalid result kind");
        if (!(result.proof instanceof Uint8Array))
          throw new HttpError(502, "solver returned a non-byte proof");
        if (result.proof.byteLength > maxProofBytes)
          throw new HttpError(502, "solver proof exceeds server bound");
        response.writeHead(200, {
          "content-type": LRAT_CONTENT_TYPE,
          "content-length": result.proof.byteLength,
        });
        response.end(result.proof);
      }
    } catch (error) {
      const status = error instanceof HttpError ? error.status : 502;
      if (response.destroyed || response.writableEnded) return;
      if (response.headersSent) {
        response.destroy();
        return;
      }
      response.writeHead(status, {
        "content-type": "text/plain; charset=utf-8",
      });
      response.end(error instanceof Error ? error.message : String(error));
    }
  });
}

function serializeModel(model: unknown, limit: number): string {
  if (!(model instanceof BigInt64Array) && !Array.isArray(model))
    throw new HttpError(502, "solver returned a non-integer model");
  const length = model.length;
  if (!Number.isSafeInteger(length) || length < 0 || length > limit)
    throw new HttpError(502, "solver model exceeds server bound");
  const parts: string[] = [];
  let bytes = 2;
  for (let index = 0; index < length; index += 1) {
    const value = model[index];
    if (typeof value !== "bigint" || value === 0n)
      throw new HttpError(502, "solver returned an invalid model literal");
    if (value < -(1n << 63n) || value >= 1n << 63n)
      throw new HttpError(502, "solver returned an out-of-range model literal");
    const text = String(value);
    bytes += Buffer.byteLength(text) + 1;
    if (bytes > limit * 21 + 2)
      throw new HttpError(502, "solver model exceeds server byte bound");
    parts.push(text);
  }
  return parts.length === 0 ? "0\n" : `${parts.join(" ")} 0\n`;
}

async function abortable<T>(
  promise: Promise<T>,
  signal: AbortSignal,
): Promise<T> {
  if (signal.aborted) throw new Error("SAT request aborted");
  let rejectAbort: ((reason: Error) => void) | undefined;
  const aborted = new Promise<never>((_resolve, reject) => {
    rejectAbort = reject;
  });
  const onAbort = () => rejectAbort?.(new Error("SAT request aborted"));
  signal.addEventListener("abort", onAbort, { once: true });
  try {
    const result = await Promise.race([promise, aborted]);
    if (signal.aborted) throw new Error("SAT request aborted");
    return result;
  } finally {
    signal.removeEventListener("abort", onAbort);
  }
}

function boundedInteger(
  value: number,
  name: string,
  maximum: number,
  positive = false,
): void {
  if (
    !Number.isSafeInteger(value) ||
    value < (positive ? 1 : 0) ||
    value > maximum
  ) {
    throw new Error(`invalid CaDiCaL ${name} bound`);
  }
}

class HttpError extends Error {
  constructor(
    readonly status: number,
    message: string,
  ) {
    super(message);
  }
}
