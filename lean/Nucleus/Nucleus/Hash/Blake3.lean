import Nucleus.Bytes
import Nucleus.Hash.Basic
import Mathlib.Data.Fintype.Prod

/-! # BLAKE3-shaped Merkle hashing -/

namespace Nucleus.Blake3

abbrev Block := Hash 512

structure Params where
  cv : Hash 256
  counter : Hash 64
  blockLength : Fin 65
  flags : Hash 8
  deriving DecidableEq

private def paramsEquiv : Params ≃ Hash 256 × Hash 64 × Fin 65 × Hash 8 where
  toFun params := (params.cv, params.counter, params.blockLength, params.flags)
  invFun values := ⟨values.1, values.2.1, values.2.2.1, values.2.2.2⟩
  left_inv params := by cases params; rfl
  right_inv values := by rcases values with ⟨_, _, _, _⟩; rfl

noncomputable instance : Fintype Params := Fintype.ofEquiv _ paramsEquiv.symm

structure Compression where
  compress : Params → Block → Hash 256

instance : CoeFun Compression fun _ => Params → Block → Hash 256 :=
  ⟨Compression.compress⟩

structure Cv where
  value : Hash 256
  deriving DecidableEq

structure Digest where
  value : Hash 256
  deriving DecidableEq

def chunkStart : Hash 8 := 1
def chunkEnd : Hash 8 := 2
def parent : Hash 8 := 4
def root : Hash 8 := 8

def blockOfBytes (bytes : List UInt8) : Block :=
  BitVec.ofNat 512 <| bytes.foldl (fun value byte => value * 256 + byte.toNat) 0

def chunks (bytes : Bytes) : List (List UInt8) :=
  match bytes.data.toList with
  | [] => [[]]
  | values => List.toChunks 1024 values

def chunkBlocks (bytes : List UInt8) : List (List UInt8) :=
  match bytes with
  | [] => [[]]
  | values => List.toChunks 64 values

def blockCount (byteLength : Nat) : Nat := max 1 ((byteLength + 63) / 64)

def chunkCount (byteLength : Nat) : Nat := max 1 ((byteLength + 1023) / 1024)

/-- Leaf and parent compression calls made by the tree. -/
def callBudget (byteLength : Nat) : Nat :=
  blockCount byteLength + chunkCount byteLength - 1

@[simp] theorem callBudget_zero : callBudget 0 = 1 := by
  decide

theorem callBudget_pos (byteLength : Nat) : 0 < callBudget byteLength := by
  unfold callBudget blockCount chunkCount
  omega

def leafParams (previous : Hash 256) (chunkIndex blockIndex length : Nat)
    (last : Bool) : Params where
  cv := previous
  counter := BitVec.ofNat 64 chunkIndex
  blockLength := ⟨min length 64, by omega⟩
  flags := (if blockIndex = 0 then chunkStart else 0) ||| (if last then chunkEnd else 0)

def parentParams : Params where
  cv := 0
  counter := 0
  blockLength := ⟨64, by omega⟩
  flags := parent

def rootParams : Params := { parentParams with flags := parent ||| root }

namespace Cv

def fromChunk (compress : Compression) (initial : Hash 256) (chunkIndex : Nat)
    (bytes : List UInt8) : Cv :=
  let input := chunkBlocks bytes
  input.zipIdx.foldl
    (fun previous item =>
      ⟨compress (leafParams previous.value chunkIndex item.2 item.1.length
        (decide (item.2 + 1 = input.length))) (blockOfBytes item.1)⟩) ⟨initial⟩

def chunkHashes (compress : Compression) (initial : Hash 256)
    (bytes : Bytes) : List Cv :=
  (chunks bytes).zipIdx.map fun item => fromChunk compress initial item.2 item.1

def merge (left right : Cv) (compress : Compression) : Cv :=
  ⟨compress parentParams (left.value ++ right.value)⟩

def root (left right : Cv) (compress : Compression) : Digest :=
  ⟨compress rootParams (left.value ++ right.value)⟩

end Cv

def coalesce (compress : Compression) (head : Cv) (tail : List Cv) : Digest :=
  match tail.reverse with
  | [] => ⟨head.value⟩
  | last :: reversePrefix =>
      let left := reversePrefix.reverse.foldl (fun left right => left.merge right compress) head
      left.root last compress

namespace Compression

def hash (compress : Compression) (initial : Hash 256) (bytes : Bytes) : Digest :=
  match Cv.chunkHashes compress initial bytes with
  | [] => ⟨initial⟩
  | head :: tail => coalesce compress head tail

end Compression

end Nucleus.Blake3
