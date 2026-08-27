import Nucleus.Cbor.Wire

namespace Nucleus.CborWire

-- These executable parser examples are tests, not exported proof declarations.
set_option linter.style.nativeDecide false

private def wire (xs : List UInt8) : Bytes := ⟨xs.toByteArray⟩

example : parse? (wire [0x00]) = some (.primitive (.integer (.unsigned 0))) := by native_decide
example : parse? (wire [0x38, 0xff]) = some (.primitive (.integer (.negative 255))) := by
  native_decide
example : parse? (wire [0x5f, 0x42, 1, 2, 0x41, 3, 0xff]) =
    some (.primitive (.bytes (wire [1, 2, 3]))) := by native_decide
example : parse? (wire [0x7f, 0x61, 0x61, 0x61, 0x62, 0xff]) =
    some (.primitive (.text "ab")) := by native_decide
example : parse? (wire [0x9f, 1, 2, 0xff]) =
    some (.array (.arrayCons (.primitive (.integer (.unsigned 1)))
      (.arrayCons (.primitive (.integer (.unsigned 2))) .arrayNil))) := by native_decide
example : parse? (wire [0xbf, 0x61, 0x61, 1, 0xff]) =
    some (.map (.mapCons (.primitive (.text "a"))
      (.primitive (.integer (.unsigned 1))) .mapNil)) := by native_decide
example : parse? (wire [0xd8, 42, 0x41, 0]) =
    some (.tag 42 (.primitive (.bytes (wire [0])))) := by native_decide
example : parse? (wire [0xf9, 0x3e, 0x00]) = some (.primitive (.float16 0x3e00)) := by
  native_decide
example : parse? (wire [0xfa, 0x3f, 0x80, 0, 0]) =
    some (.primitive (.float32 0x3f800000)) := by native_decide
example : parse? (wire [0xfb, 0x3f, 0xf0, 0, 0, 0, 0, 0, 0]) =
    some (.primitive (.float64 0x3ff0000000000000)) := by native_decide

example : deterministic? (.primitive (.integer (.unsigned 23))) = some (wire [0x17]) := by
  native_decide
example : deterministic? (.primitive (.integer (.unsigned 24))) = some (wire [0x18, 0x18]) := by
  native_decide
example : deterministic? (.tag 42 (.primitive (.bytes (wire [0])))) =
    some (wire [0xd8, 42, 0x41, 0]) := by native_decide

end Nucleus.CborWire
