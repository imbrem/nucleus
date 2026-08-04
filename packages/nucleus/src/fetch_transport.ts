/** Exact paths implemented by the v0 signed kernel HTTP byte transport. */
export const KERNEL_CHANNEL_PATH = "v0/channel";
export const KERNEL_INVOCATION_PATH = "v0/invocation";

/** Fixed v0 transport limits mirrored from `covalence-kernel-service`. */
export const MAX_KERNEL_CHANNEL_GRANT_BYTES = 512;
export const MAX_KERNEL_SIGNED_FRAME_BYTES = (64 << 20) + 18 + 384;

const CALLER_KEY_BYTES = 32;
const BOOTSTRAP_TOKEN_BYTES = 32;
const MAX_DIAGNOSTIC_BYTES = 4 << 10;
const BINARY_CONTENT_TYPE = "application/octet-stream";
const DEFAULT_TIMEOUT_MS = 30_000;

export interface KernelFetchOptions {
  /** Fetch implementation used for both channel admission and invocations. */
  fetch?: typeof globalThis.fetch;
  /** Per-request wall-clock timeout. Defaults to 30 seconds. */
  timeoutMs?: number;
}

/**
 * Strict, retry-free byte transport for one signed HTTP kernel endpoint.
 *
 * This class deliberately performs no signature verification and grants no
 * authority. The Rust signed-client state must authenticate its returned grant
 * and results. In particular, callers must abandon a pending invocation after
 * any `invoke` rejection and must never retry the same bytes.
 */
export class KernelFetchTransport {
  readonly #baseUrl: URL;
  readonly #fetch: typeof globalThis.fetch;
  readonly #timeoutMs: number;

  constructor(endpoint: string | URL, options: KernelFetchOptions = {}) {
    this.#baseUrl = normalizeEndpoint(endpoint);
    this.#fetch = options.fetch ?? globalThis.fetch;
    if (typeof this.#fetch !== "function")
      throw new TypeError("fetch is unavailable in this environment");
    this.#timeoutMs = options.timeoutMs ?? DEFAULT_TIMEOUT_MS;
    if (
      !Number.isSafeInteger(this.#timeoutMs) ||
      this.#timeoutMs <= 0 ||
      this.#timeoutMs > 0x7fff_ffff
    )
      throw new RangeError("kernel fetch timeout must be a positive integer");
  }

  /** Canonical endpoint URL retained as inspectable, non-authoritative route metadata. */
  get endpoint(): string {
    return this.#baseUrl.href;
  }

  /** Requests one recipient-signed channel grant for an exact caller key. */
  requestChannel(
    caller: Uint8Array,
    bootstrapToken?: Uint8Array,
  ): Promise<Uint8Array> {
    requireBytes(caller, CALLER_KEY_BYTES, "caller public key");
    if (bootstrapToken !== undefined)
      requireBytes(
        bootstrapToken,
        BOOTSTRAP_TOKEN_BYTES,
        "bootstrap token",
      );
    const headers = new Headers({ "Content-Type": BINARY_CONTENT_TYPE });
    if (bootstrapToken !== undefined)
      headers.set(
        "Authorization",
        `Nucleus-Bootstrap ${encodeHex(bootstrapToken)}`,
      );
    return this.#post(
      KERNEL_CHANNEL_PATH,
      caller,
      headers,
      MAX_KERNEL_CHANNEL_GRANT_BYTES,
    );
  }

  /**
   * Exchanges one canonical signed invocation for its canonical signed result.
   *
   * This method issues exactly one fetch and never retries or follows redirects.
   */
  invoke(invocation: Uint8Array): Promise<Uint8Array> {
    if (!(invocation instanceof Uint8Array))
      throw new TypeError("signed invocation must be a Uint8Array");
    if (invocation.byteLength > MAX_KERNEL_SIGNED_FRAME_BYTES)
      throw new RangeError("signed invocation exceeds the v0 transport limit");
    return this.#post(
      KERNEL_INVOCATION_PATH,
      invocation,
      new Headers({ "Content-Type": BINARY_CONTENT_TYPE }),
      MAX_KERNEL_SIGNED_FRAME_BYTES,
    );
  }

  async #post(
    path: string,
    body: Uint8Array,
    headers: Headers,
    responseLimit: number,
  ): Promise<Uint8Array> {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), this.#timeoutMs);
    try {
      const response = await this.#fetch(new URL(path, this.#baseUrl), {
        method: "POST",
        body: body.slice(),
        headers,
        cache: "no-store",
        credentials: "omit",
        redirect: "error",
        referrerPolicy: "no-referrer",
        signal: controller.signal,
      });

      if (response.status !== 200) {
        if (
          response.headers.get("content-type") !==
          "text/plain; charset=utf-8"
        )
          throw new Error("kernel boundary error has an unexpected Content-Type");
        if (response.headers.has("content-encoding"))
          throw new Error("kernel response Content-Encoding is forbidden");
        const diagnostic = await readBoundedBody(
          response,
          MAX_DIAGNOSTIC_BYTES,
        );
        throw new Error(
          `kernel HTTP boundary returned ${response.status}: ${new TextDecoder().decode(diagnostic)}`,
        );
      }
      if (response.headers.get("content-type") !== BINARY_CONTENT_TYPE)
        throw new Error("kernel returned an unexpected Content-Type");
      if (response.headers.has("content-encoding"))
        throw new Error("kernel response Content-Encoding is forbidden");
      return await readBoundedBody(response, responseLimit);
    } catch (error) {
      if (controller.signal.aborted)
        throw new Error("kernel fetch timed out", { cause: error });
      throw error;
    } finally {
      clearTimeout(timeout);
    }
  }
}

function normalizeEndpoint(endpoint: string | URL): URL {
  const url = new URL(endpoint);
  if (url.protocol !== "http:" && url.protocol !== "https:")
    throw new TypeError("kernel fetch endpoint must use HTTP or HTTPS");
  if (url.username !== "" || url.password !== "")
    throw new TypeError("kernel fetch endpoint must not contain credentials");
  if (url.search !== "" || url.hash !== "")
    throw new TypeError("kernel fetch endpoint must not contain a query or fragment");
  if (!url.pathname.endsWith("/")) url.pathname += "/";
  return url;
}

async function readBoundedBody(
  response: Response,
  limit: number,
): Promise<Uint8Array> {
  const declared = response.headers.get("content-length");
  if (declared === null || !/^(?:0|[1-9][0-9]*)$/u.test(declared))
    throw new Error("kernel response has no canonical Content-Length");
  const expected = Number(declared);
  if (!Number.isSafeInteger(expected) || expected > limit)
    throw new RangeError("kernel response exceeds its transport limit");
  if (response.body === null) {
    if (expected === 0) return new Uint8Array();
    throw new Error("kernel response body is missing");
  }

  const output = new Uint8Array(expected);
  const reader = response.body.getReader();
  let offset = 0;
  try {
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      if (offset + value.byteLength > expected || offset + value.byteLength > limit)
        throw new Error("kernel response exceeds its declared Content-Length");
      output.set(value, offset);
      offset += value.byteLength;
    }
  } catch (error) {
    await reader.cancel(error).catch(() => undefined);
    throw error;
  }
  if (offset !== expected)
    throw new Error("kernel response is shorter than its Content-Length");
  return output;
}

function requireBytes(value: Uint8Array, length: number, name: string): void {
  if (!(value instanceof Uint8Array) || value.byteLength !== length)
    throw new TypeError(`${name} must contain exactly ${length} bytes`);
}

function encodeHex(bytes: Uint8Array): string {
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, "0")).join(
    "",
  );
}
