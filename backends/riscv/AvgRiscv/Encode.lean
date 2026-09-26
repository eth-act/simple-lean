import AvgRiscv.Impl
import AssemblyRiscv

namespace AvgRiscv

open RiscvZkvm.Rv64
open RiscvZkvm.Interpreter (decode)
open AssemblyRiscv (encodeProgram wordBytesLE wordsFromBytesLE)


/-- Words extracted from the actual program; the proof rules out encoding failure. -/
def avgWords : List (BitVec 32) :=
  (encodeProgram avgProgram).get (by rfl)

/-- The exported words are the successful result of encoding `avgProgram`. -/
theorem avgProgram_encoded : encodeProgram avgProgram = some avgWords := by
  rfl

/-- The dependency's executable decoder recovers exactly the proved instruction list. -/
theorem avgWords_decode : avgWords.map decode = avgProgram.map some := by
  rfl

/-- Every successful encoding of this program decodes to the original instructions. -/
theorem avgProgram_decode (words : List (BitVec 32))
    (h : encodeProgram avgProgram = some words) :
    words.map decode = avgProgram.map some := by
  have hw : words = avgWords := Option.some.inj (h.symm.trans avgProgram_encoded)
  subst words
  exact avgWords_decode


/-- Serialization used by the exporter preserves every word of the proved program. -/
theorem avgWords_bytes_roundtrip :
    wordsFromBytesLE (avgWords.flatMap wordBytesLE) = some avgWords := by
  rfl

end AvgRiscv
