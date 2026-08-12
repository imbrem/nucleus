/** A file exposed to the SQLite component. */
export interface VfsFile {
  size(): bigint | Promise<bigint>;
  readAt(offset: bigint, length: number): Uint8Array | Promise<Uint8Array>;
  close?(): void;
}

/** The deliberately small, read-only host boundary used by SQLite. */
export interface ReadOnlyVfs {
  open(name: string): VfsFile | Promise<VfsFile>;
}

/** Errors understood by the component's read-only VFS interface. */
export type VfsError =
  | "not-found"
  | "invalid-name"
  | "invalid-range"
  | "too-large"
  | "backend";

let active: ReadOnlyVfs | undefined;

/** The resource class imported by the generated component. */
export class File {
  constructor(private readonly file: VfsFile) {}

  async size(): Promise<bigint> {
    try {
      return await this.file.size();
    } catch (error) {
      throw normalizeError(error);
    }
  }

  async readAt(offset: bigint, length: number): Promise<Uint8Array> {
    try {
      return await this.file.readAt(offset, length);
    } catch (error) {
      throw normalizeError(error);
    }
  }

  [Symbol.dispose](): void {
    this.file.close?.();
  }
}

/** Called by the generated component import. */
export async function open(name: string): Promise<File> {
  if (!active) throw "backend";
  try {
    return new File(await active.open(name));
  } catch (error) {
    throw normalizeError(error);
  }
}

function normalizeError(error: unknown): VfsError {
  switch (error) {
    case "not-found":
    case "invalid-name":
    case "invalid-range":
    case "too-large":
    case "backend":
      return error;
    default:
      return "backend";
  }
}

/** Installs a VFS for one shell run. Runs are serialized by the caller. */
export async function withVfs<T>(
  vfs: ReadOnlyVfs,
  operation: () => Promise<T>,
): Promise<T> {
  if (active) throw new Error("an SQLite shell is already running");
  active = vfs;
  try {
    return await operation();
  } finally {
    active = undefined;
  }
}
