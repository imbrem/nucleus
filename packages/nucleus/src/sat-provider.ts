/** Canonical DIMACS and operational response bounds given to an untrusted solver. */
export interface SatRequest {
  /** Exact canonical problem identity retained by the consuming continuation. */
  readonly problem: Uint8Array;
  readonly dimacs: Uint8Array;
  readonly limits: {
    readonly maxModelLiterals: number;
    readonly maxProofBytes: number;
  };
  readonly proof: {
    readonly format: "binary-lrat";
    /** Explicit diagnostic opt-in; ordinary providers leave this false. */
    readonly diagnosticAsciiLrat?: boolean;
  };
}

/** An untrusted solver claim. It carries no logical authority. */
export type SatResult =
  | {
      readonly kind: "sat";
      readonly problem: Uint8Array;
      readonly model: readonly bigint[] | BigInt64Array;
    }
  | {
      readonly kind: "unsat";
      readonly problem: Uint8Array;
      readonly proof: Uint8Array;
      readonly format: "binary-lrat" | "ascii-lrat";
    }
  | {
      readonly kind: "unknown";
      readonly problem: Uint8Array;
      readonly reason?: string;
    };

/** Transport-neutral capability for a completely untrusted SAT solver. */
export interface SatSolver {
  solve(request: SatRequest, signal?: AbortSignal): Promise<SatResult>;
}
