import { request as requestHttp } from "node:http";

const CHANNEL_PATH = "/v0/channel";
const INVOCATION_PATH = "/v0/invocation";
const CHANNEL_BODY_BYTES = 32;
const MAX_SIGNED_FRAME_BYTES = (64 << 20) + 18 + 384;
const MAX_DIAGNOSTIC_BYTES = 4 << 10;
const BINARY_CONTENT_TYPE = "application/octet-stream";
const TEXT_CONTENT_TYPE = "text/plain; charset=utf-8";

/**
 * Builds the test-only same-origin relay used by browser/native-kernel E2E tests.
 *
 * Mount the returned handler before the static-file handler. It recognizes only
 * `${mountPath}v0/channel` and `${mountPath}v0/invocation`, forwards each request
 * once to one fixed numeric-loopback kernel, and returns `false` for every other
 * path. The relay is deliberately not a security boundary: canonical signatures
 * are created and checked by Rust on either side of these opaque bytes. It never
 * accepts credentials, so callers must already be allow-listed by public key.
 */
export function createKernelTestRelay(upstream, mountPath = "/kernel/") {
  const endpoint = normalizeUpstream(upstream);
  const mount = normalizeMount(mountPath);
  const counts = { channel: 0, invocation: 0 };

  const relay = async function relayKernelRequest(incoming, outgoing) {
    const requestUrl = new URL(incoming.url ?? "/", "http://test.invalid");
    const { pathname } = requestUrl;
    if (!pathname.startsWith(mount)) return false;
    if (requestUrl.search !== "" || requestUrl.hash !== "") {
      writeDiagnostic(outgoing, 400, "kernel relay forbids query and fragment");
      return true;
    }

    const upstreamPath = `/${pathname.slice(mount.length)}`;
    const limit =
      upstreamPath === CHANNEL_PATH
        ? CHANNEL_BODY_BYTES
        : upstreamPath === INVOCATION_PATH
          ? MAX_SIGNED_FRAME_BYTES
          : undefined;
    if (limit === undefined) {
      writeDiagnostic(outgoing, 404, "unknown kernel relay path");
      return true;
    }
    if (incoming.method !== "POST") {
      writeDiagnostic(outgoing, 405, "kernel relay accepts POST only");
      return true;
    }
    if (incoming.headers["content-type"] !== BINARY_CONTENT_TYPE) {
      writeDiagnostic(outgoing, 415, "kernel relay requires binary content");
      return true;
    }
    if (incoming.headers.authorization !== undefined) {
      writeDiagnostic(outgoing, 400, "kernel relay forbids authorization");
      return true;
    }

    try {
      const body = await readExactBody(incoming, limit);
      if (
        upstreamPath === CHANNEL_PATH &&
        body.byteLength !== CHANNEL_BODY_BYTES
      )
        throw new Error("channel caller key must contain exactly 32 bytes");
      if (upstreamPath === CHANNEL_PATH) counts.channel += 1;
      else counts.invocation += 1;
      const response = await postOnce(endpoint, upstreamPath, body);
      outgoing.writeHead(response.status, {
        "content-type": response.contentType,
        "content-length": String(response.body.byteLength),
        "cache-control": "no-store",
      });
      outgoing.end(response.body);
    } catch (error) {
      writeDiagnostic(
        outgoing,
        502,
        error instanceof Error ? error.message : "kernel relay failed",
      );
    }
    return true;
  };
  relay.counts = counts;
  return relay;
}

function normalizeUpstream(upstream) {
  const endpoint = new URL(upstream);
  if (endpoint.protocol !== "http:")
    throw new TypeError("test kernel relay requires plain loopback HTTP");
  if (endpoint.hostname !== "127.0.0.1" && endpoint.hostname !== "[::1]")
    throw new TypeError("test kernel relay upstream must be numeric loopback");
  if (
    endpoint.username !== "" ||
    endpoint.password !== "" ||
    endpoint.search !== "" ||
    endpoint.hash !== "" ||
    endpoint.pathname !== "/"
  )
    throw new TypeError("test kernel relay upstream must be an origin only");
  return endpoint;
}

function normalizeMount(mountPath) {
  if (
    !mountPath.startsWith("/") ||
    mountPath.includes("?") ||
    mountPath.includes("#")
  )
    throw new TypeError("kernel relay mount must be an absolute path");
  return mountPath.endsWith("/") ? mountPath : `${mountPath}/`;
}

async function readExactBody(incoming, limit) {
  const declared = incoming.headers["content-length"];
  if (typeof declared !== "string" || !/^(?:0|[1-9][0-9]*)$/u.test(declared))
    throw new Error("kernel relay request requires canonical Content-Length");
  const expected = Number(declared);
  if (!Number.isSafeInteger(expected) || expected > limit)
    throw new Error("kernel relay request exceeds its endpoint limit");

  const chunks = [];
  let received = 0;
  for await (const chunk of incoming) {
    received += chunk.byteLength;
    if (received > expected || received > limit)
      throw new Error("kernel relay request exceeds its declared length");
    chunks.push(chunk);
  }
  if (received !== expected)
    throw new Error("kernel relay request is shorter than its declared length");
  return Buffer.concat(chunks, received);
}

function postOnce(endpoint, path, body) {
  return new Promise((resolve, reject) => {
    const headers = {
      "content-type": BINARY_CONTENT_TYPE,
      "content-length": String(body.byteLength),
      connection: "close",
    };
    const request = requestHttp(
      endpoint,
      { method: "POST", path, headers, agent: false },
      async (response) => {
        try {
          const status = response.statusCode ?? 502;
          const contentType = response.headers["content-type"];
          const limit =
            status === 200 ? MAX_SIGNED_FRAME_BYTES : MAX_DIAGNOSTIC_BYTES;
          if (
            contentType !== BINARY_CONTENT_TYPE &&
            contentType !== TEXT_CONTENT_TYPE
          )
            throw new Error("kernel returned an unexpected Content-Type");
          const responseBody = await readExactBody(response, limit);
          resolve({ status, contentType, body: responseBody });
        } catch (error) {
          reject(error);
        }
      },
    );
    request.once("error", reject);
    request.end(body);
  });
}

function writeDiagnostic(outgoing, status, diagnostic) {
  const body = Buffer.from(diagnostic).subarray(0, MAX_DIAGNOSTIC_BYTES);
  outgoing.writeHead(status, {
    "content-type": TEXT_CONTENT_TYPE,
    "content-length": String(body.byteLength),
    "cache-control": "no-store",
  });
  outgoing.end(body);
}
