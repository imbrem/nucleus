import {
  type WebRemoteProducedHolComponent,
  WebSignedKernelSession,
} from "../generated/nucleus.js";

export class SignedKernelTransportError extends Error {
  constructor(
    message: string,
    readonly outcomeUnknown: boolean,
    cause?: unknown,
  ) {
    super(message, { cause });
    this.name = "SignedKernelTransportError";
  }
}

export function acceptStatefulReply<T>(accept: () => T): T {
  try {
    return accept();
  } catch (error) {
    throw new SignedKernelTransportError(
      `native signed-kernel reply could not be accepted: ${String(error)}`,
      true,
      error,
    );
  }
}

export async function runNativeHttpHashSelectedArtifact(options: {
  endpoint: string;
  expectedPublicKey: Uint8Array;
  component: string;
  timeoutMs: number;
}): Promise<WebRemoteProducedHolComponent> {
  if (
    !/^[0-9a-f]{64}$/.test(options.component) ||
    options.expectedPublicKey.byteLength !== 32 ||
    !Number.isSafeInteger(options.timeoutMs) ||
    options.timeoutMs <= 0
  ) {
    throw new Error(
      "component must be canonical O256, timeout positive, and endpoint key 32 bytes",
    );
  }
  const description = await signedFetch(
    options.endpoint,
    WebSignedKernelSession.describe_request(),
    options.timeoutMs,
    false,
  );
  const session = WebSignedKernelSession.begin(
    options.expectedPublicKey,
    description,
  );
  let produced: WebRemoteProducedHolComponent | undefined;
  try {
    const accepted = await signedFetch(
      options.endpoint,
      session.session_request(),
      options.timeoutMs,
      true,
    );
    acceptStatefulReply(() => session.accept_session(accepted));
    const producedReply = await signedFetch(
      options.endpoint,
      session.run_hol_proof_component_command(options.component),
      options.timeoutMs,
      true,
    );
    produced = acceptStatefulReply(() =>
      session.accept_hol_proof_component(producedReply, options.component),
    );
    if (produced.component() !== options.component) {
      throw new SignedKernelTransportError(
        "signed component result changed the selected digest",
        true,
      );
    }
    const closed = await signedFetch(
      options.endpoint,
      session.close_session_command(),
      options.timeoutMs,
      true,
    );
    acceptStatefulReply(() => session.accept_session_closed(closed));
    const result = produced;
    produced = undefined;
    return result;
  } finally {
    produced?.free();
    session.free();
  }
}

export async function signedFetch(
  endpoint: string,
  body: Uint8Array,
  timeoutMs: number,
  outcomeUnknown: boolean,
): Promise<Uint8Array> {
  if (body.byteLength > WebSignedKernelSession.max_message_bytes()) {
    throw new SignedKernelTransportError("signed request exceeds bound", false);
  }
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), timeoutMs);
  try {
    const response = await fetch(endpoint, {
      method: "POST",
      mode: "cors",
      body: body.slice().buffer as ArrayBuffer,
      redirect: "error",
      credentials: "omit",
      cache: "no-store",
      referrerPolicy: "no-referrer",
      signal: controller.signal,
      headers: { "content-type": "application/octet-stream" },
    });
    if (!response.ok)
      throw new Error(`native kernel HTTP status ${response.status}`);
    return await readBoundedResponse(
      response,
      WebSignedKernelSession.max_message_bytes(),
    );
  } catch (error) {
    throw new SignedKernelTransportError(
      `native signed-kernel request failed: ${String(error)}`,
      outcomeUnknown,
      error,
    );
  } finally {
    clearTimeout(timeout);
  }
}

async function readBoundedResponse(
  response: Response,
  limit: number,
): Promise<Uint8Array> {
  const contentType = response.headers.get("content-type");
  const mediaType = contentType?.split(";", 1)[0]?.trim().toLowerCase();
  if (mediaType !== "application/octet-stream") {
    throw new Error("signed response is not application/octet-stream");
  }
  const length = response.headers.get("content-length");
  if (length !== null) {
    const parsed = Number(length);
    if (!Number.isSafeInteger(parsed) || parsed < 0 || parsed > limit) {
      throw new Error(`signed response length exceeds ${limit} bytes`);
    }
  }
  if (response.body === null) throw new Error("signed response has no body");
  const reader = response.body.getReader();
  const chunks: Uint8Array[] = [];
  let total = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) break;
    total += value.byteLength;
    if (total > limit) {
      await reader.cancel();
      throw new Error(`signed response exceeds ${limit} bytes`);
    }
    chunks.push(value);
  }
  if (length !== null && total !== Number(length)) {
    throw new Error("signed response body is truncated");
  }
  const bytes = new Uint8Array(total);
  let offset = 0;
  for (const chunk of chunks) {
    bytes.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return bytes;
}
