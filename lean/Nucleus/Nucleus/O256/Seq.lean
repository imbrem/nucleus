import Nucleus.HashSeq
import Nucleus.O256.Basic

/-! # O256 sequences -/

namespace Nucleus.O256

/-- Fixed-width O256 encoding. -/
def encoding : HashSeq.Encoding O256 where
  width := 32
  width_pos := by omega
  encode := bytes
  encode_length := bytes_length

/-- Bare concatenation of O256 values. -/
def encodeSeq (values : HashSeq.Seq O256) : List UInt8 :=
  HashSeq.encode encoding values

@[simp] theorem encodeSeq_length (values : HashSeq.Seq O256) :
    (encodeSeq values).length = 32 * values.length :=
  HashSeq.encode_length encoding values

end Nucleus.O256
