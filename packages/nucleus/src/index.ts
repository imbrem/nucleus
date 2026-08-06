import init, { Kernel } from "../generated/nucleus.js";

export { init, Kernel };

/** How an object was obtained, for display. */
export type Origin = "local" | string;

/**
 * Fetches an object from a remote kernel and admits it, verifying as it goes.
 *
 * The URL says where bytes might be; the address says whether they are the
 * right ones. `Kernel.admit` refuses anything that does not hash to `address`,
 * so a wrong or hostile server is caught here rather than believed.
 */
export async function fetchInto(
  kernel: Kernel,
  baseUrl: string,
  address: string,
): Promise<number> {
  const response = await fetch(`${baseUrl.replace(/\/$/, "")}/cas/${address}`);
  if (!response.ok) {
    throw new Error(`kernel returned ${response.status} for ${address}`);
  }
  const bytes = new Uint8Array(await response.arrayBuffer());
  kernel.admit(address, bytes);
  return bytes.length;
}

/**
 * Reads one range from a remote kernel without admitting it.
 *
 * Present to show that the HTTP kernel really is ranged, which is what a VFS
 * needs and what makes whole-object fetching unnecessary once range proofs
 * exist. Until then a ranged read cannot be verified, so this returns bytes
 * for inspection and deliberately does not put them in the store.
 */
export async function fetchRange(
  baseUrl: string,
  address: string,
  start: number,
  end: number,
): Promise<{ bytes: Uint8Array; contentRange: string | null }> {
  const response = await fetch(`${baseUrl.replace(/\/$/, "")}/cas/${address}`, {
    headers: { Range: `bytes=${start}-${end}` },
  });
  if (response.status !== 206) {
    throw new Error(`expected 206 Partial Content, got ${response.status}`);
  }
  return {
    bytes: new Uint8Array(await response.arrayBuffer()),
    contentRange: response.headers.get("content-range"),
  };
}
