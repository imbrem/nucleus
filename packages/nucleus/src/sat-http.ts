import type { SatRequest, SatResult, SatSolver } from "./index.js";

export const DIMACS_CONTENT_TYPE = "application/dimacs";
export const MODEL_CONTENT_TYPE = "application/vnd.nucleus.sat-model";
export const LRAT_CONTENT_TYPE = "application/vnd.nucleus.lrat";
const MAX_RESPONSE_BYTES = 256 * 1024 * 1024;
const MAX_MODEL_LITERALS = 10_000_000;

/** An ordinary HTTP adapter for an untrusted SAT service. */
export class HttpSatSolver implements SatSolver {
  readonly #url: string;

  constructor(url: string | URL) {
    this.#url = String(url);
  }

  async solve(request: SatRequest, signal?: AbortSignal): Promise<SatResult> {
    boundedLimit(request.limits.maxModelLiterals, MAX_MODEL_LITERALS, "model");
    boundedLimit(request.limits.maxProofBytes, MAX_RESPONSE_BYTES, "proof");
    const response = await fetch(this.#url, {
      method: "POST",
      headers: {
        "content-type": DIMACS_CONTENT_TYPE,
        accept: `${MODEL_CONTENT_TYPE}, ${LRAT_CONTENT_TYPE}`,
      },
      body: Uint8Array.from(request.dimacs).buffer,
      signal,
    });
    if (!response.ok) {
      await response.body?.cancel();
      throw new Error(`SAT service returned HTTP ${response.status}`);
    }

    const type = response.headers.get("content-type")?.split(";", 1)[0];
    if (type === MODEL_CONTENT_TYPE) {
      const bytes = await readBounded(response, modelByteLimit(request));
      return { kind: "sat", model: parseModel(bytes, request) };
    }
    if (type === LRAT_CONTENT_TYPE) {
      return {
        kind: "unsat",
        proof: await readBounded(response, request.limits.maxProofBytes),
      };
    }
    await response.body?.cancel();
    throw new Error(
      `SAT service returned unsupported content type ${type ?? ""}`,
    );
  }
}

function boundedLimit(value: number, maximum: number, name: string): void {
  if (!Number.isSafeInteger(value) || value < 0 || value > maximum) {
    throw new Error(`invalid SAT ${name} response bound`);
  }
}

function modelByteLimit(request: SatRequest): number {
  // A signed i64 plus whitespace. The REPL independently checks literal count.
  return Math.min(
    Number.MAX_SAFE_INTEGER,
    request.limits.maxModelLiterals * 21 + 2,
  );
}

async function readBounded(
  response: Response,
  limit: number,
): Promise<Uint8Array> {
  const stated = response.headers.get("content-length");
  if (stated !== null && (!/^\d+$/.test(stated) || Number(stated) > limit)) {
    await response.body?.cancel();
    throw new Error("SAT service response exceeds its bound");
  }
  if (!response.body) return new Uint8Array();

  const reader = response.body.getReader();
  const chunks: Uint8Array[] = [];
  let length = 0;
  try {
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      length += value.byteLength;
      if (length > limit)
        throw new Error("SAT service response exceeds its bound");
      chunks.push(value);
    }
  } catch (error) {
    await reader.cancel().catch(() => undefined);
    throw error;
  } finally {
    reader.releaseLock();
  }
  const result = new Uint8Array(length);
  let offset = 0;
  for (const chunk of chunks) {
    result.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return result;
}

function parseModel(bytes: Uint8Array, request: SatRequest): bigint[] {
  const text = new TextDecoder("utf-8", { fatal: true }).decode(bytes);
  if (!/^[-+0-9\t\n\r ]*$/.test(text)) {
    throw new Error("SAT service returned a malformed model");
  }
  const words = text.trim().split(/\s+/).filter(Boolean);
  if (words.length > request.limits.maxModelLiterals + 1) {
    throw new Error("SAT service model exceeds its response bound");
  }
  const model: bigint[] = [];
  let terminated = false;
  for (const word of words) {
    if (!/^-?(?:0|[1-9][0-9]*)$/.test(word)) {
      throw new Error("SAT service returned a malformed model");
    }
    const literal = BigInt(word);
    if (literal === 0n) {
      if (terminated)
        throw new Error("SAT service returned duplicate model terminators");
      terminated = true;
      continue;
    }
    if (terminated)
      throw new Error("SAT service returned data after model terminator");
    if (literal < -(1n << 63n) || literal >= 1n << 63n) {
      throw new Error("SAT service returned an out-of-range model literal");
    }
    model.push(literal);
  }
  if (!terminated) throw new Error("SAT service model has no terminator");
  return model;
}
