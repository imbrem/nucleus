import init, { WebSignedKernelService } from "../generated/nucleus.js";

type Request = { id: number; bytes: Uint8Array };

const service = init().then(() => new WebSignedKernelService());

void service.then((endpoint) => {
  const publicKey = endpoint.public_key();
  globalThis.postMessage(
    { kind: "ready", publicKey },
    { transfer: [publicKey.buffer as ArrayBuffer] },
  );
});

globalThis.addEventListener(
  "message",
  async ({ data }: MessageEvent<Request>) => {
    try {
      const endpoint = await service;
      const bytes = endpoint.handle(data.bytes);
      globalThis.postMessage(
        { id: data.id, ok: true, bytes },
        { transfer: [bytes.buffer as ArrayBuffer] },
      );
    } catch (error) {
      globalThis.postMessage({
        id: data.id,
        ok: false,
        error: error instanceof Error ? error.message : String(error),
      });
    }
  },
);
