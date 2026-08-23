import {
  ProofKernel as RawProofKernel,
  hashBytes,
} from "../generated/nucleus.js";

export type SynRel = "syn" | "alpha" | "conv";

export interface ProofStats {
  rows: bigint;
  synFacts: bigint;
}

/** A host-owned immutable byte buffer. */
export class Bytes {
  readonly #value: Uint8Array;

  constructor(value: Uint8Array) {
    this.#value = value.slice();
  }

  len(): bigint {
    return BigInt(this.#value.length);
  }

  toList(): Uint8Array {
    return this.#value.slice();
  }

  slice(start: bigint, end: bigint): Bytes {
    const first = checkedIndex(start, "slice start");
    const last = checkedIndex(end, "slice end");
    if (first > last || last > this.#value.length) {
      throw new Error("slice lies outside the byte buffer");
    }
    return new Bytes(this.#value.subarray(first, last));
  }

  blob(): Blob {
    return Blob.fromBytes(this.#value);
  }

  [Symbol.dispose](): void {}
}

/** A checked whole-object CAS fact `(address, bytes)`. */
export class Blob {
  readonly #address: Uint8Array;
  readonly #value: Uint8Array;

  private constructor(address: Uint8Array, value: Uint8Array) {
    this.#address = address;
    this.#value = value;
  }

  static fromBytes(value: Uint8Array): Blob {
    const bytes = value.slice();
    return new Blob(hashBytes(bytes), bytes);
  }

  static check(address: Uint8Array, value: Bytes): Blob {
    const bytes = value.toList();
    const computed = hashBytes(bytes);
    if (!equalBytes(address, computed)) {
      throw new Error(
        `claimed hash ${hex(address)} does not match computed hash ${hex(computed)}`,
      );
    }
    return new Blob(computed, bytes);
  }

  address(): Uint8Array {
    return this.#address.slice();
  }

  bytes(): Bytes {
    return new Bytes(this.#value);
  }

  len(): bigint {
    return BigInt(this.#value.length);
  }

  [Symbol.dispose](): void {}
}

/** A component-private insertion-ordered checked CAS. */
export class IndexCas {
  readonly #objects: Array<Blob | undefined> = [];
  readonly #ids = new Map<string, bigint>();

  insert(value: Blob): bigint {
    const address = hex(value.address());
    const present = this.#ids.get(address);
    if (present !== undefined) return present;
    const id = BigInt(this.#objects.length);
    this.#objects.push(value);
    this.#ids.set(address, id);
    return id;
  }

  put(value: Bytes): bigint {
    return this.insert(value.blob());
  }

  get(object: bigint): Blob | undefined {
    const index = checkedIndex(object, "CAS object ID");
    return this.#objects[index];
  }

  find(address: Uint8Array): bigint | undefined {
    checkedAddress(address);
    return this.#ids.get(hex(address));
  }

  remove(address: Uint8Array): boolean {
    checkedAddress(address);
    const key = hex(address);
    const id = this.#ids.get(key);
    if (id === undefined) return false;
    this.#objects[checkedIndex(id, "CAS object ID")] = undefined;
    this.#ids.delete(key);
    return true;
  }

  len(): bigint {
    return BigInt(this.#ids.size);
  }

  [Symbol.dispose](): void {}
}

/** A checked kernel resource returned by a standard proof component. */
export class ProofKernel {
  readonly #kernel: RawProofKernel;

  constructor() {
    this.#kernel = new RawProofKernel();
    return new Proxy(this, {
      get(target, property) {
        const member = Reflect.get(target, property, target) as unknown;
        if (member !== undefined) {
          return typeof member === "function" ? member.bind(target) : member;
        }
        // Promise resolution probes this property on every returned object.
        if (property === "then") return undefined;
        if (typeof property === "string") {
          return () => unsupported(`kernel.${property}`);
        }
        return undefined;
      },
    });
  }

  kindStar(): bigint {
    return this.#kernel.kindStar();
  }

  boolType(star: bigint): bigint {
    return this.#kernel.boolType(star);
  }

  boolLit(boolType: bigint, value: boolean): bigint {
    return this.#kernel.boolLit(boolType, value);
  }

  synFactCount(): bigint {
    return this.#kernel.synFactCount();
  }

  removeSynFact(fact: bigint): boolean {
    return this.#kernel.removeSynFact(fact);
  }

  truncateSynFacts(len: bigint): void {
    this.#kernel.truncateSynFacts(len);
  }

  synRefl(relation: SynRel, input: bigint, target?: bigint): bigint {
    return this.#kernel.synRefl(relationCode(relation), input, target);
  }

  unionSynFact(fact: bigint): void {
    this.#kernel.unionSynFact(fact);
  }

  /** The O256 hash of the current CBOR arena encoding. */
  addr(): string {
    return this.#kernel.addr();
  }

  stats(): ProofStats {
    return {
      rows: this.#kernel.rowCount(),
      synFacts: this.#kernel.synFactCount(),
    };
  }

  /** Materializes the raw arena's diagnostic JSON only when requested. */
  debugJson(): unknown {
    return JSON.parse(this.#kernel.debugJson()) as unknown;
  }

  [Symbol.dispose](): void {
    this.#kernel.free();
  }
}

class Arena {
  constructor() {
    unsupported("arena resource");
  }
}

class Table {
  private constructor() {
    unsupported("table resource");
  }
}

const defaultCas = new IndexCas();

/** Imports supplied to a transpiled `nucleus:proof/standard-proof` component. */
export const proofHost = {
  Arena,
  Blob,
  Bytes,
  IndexCas,
  Kernel: ProofKernel,
  Table,
  casInsert(value: Blob): bigint {
    return defaultCas.insert(value);
  },
  casPut(value: Bytes): bigint {
    return defaultCas.put(value);
  },
  casGet(object: bigint): Blob | undefined {
    return defaultCas.get(object);
  },
  casFind(address: Uint8Array): bigint | undefined {
    return defaultCas.find(address);
  },
};

function relationCode(relation: SynRel): number {
  switch (relation) {
    case "syn":
      return 0;
    case "alpha":
      return 1;
    case "conv":
      return 2;
  }
}

function checkedAddress(value: Uint8Array): void {
  if (value.length !== 32) {
    throw new Error(`CAS addresses contain 32 bytes, got ${value.length}`);
  }
}

function checkedIndex(value: bigint, description: string): number {
  if (value < 0n || value > BigInt(Number.MAX_SAFE_INTEGER)) {
    throw new Error(`${description} does not fit in JavaScript's index space`);
  }
  return Number(value);
}

function equalBytes(left: Uint8Array, right: Uint8Array): boolean {
  return (
    left.length === right.length &&
    left.every((value, index) => value === right[index])
  );
}

function hex(value: Uint8Array): string {
  return Array.from(value, (byte) => byte.toString(16).padStart(2, "0")).join(
    "",
  );
}

function unsupported(operation: string): never {
  throw new Error(`${operation} is not implemented by the browser proof host`);
}
