/-!
# Specification: the average of two `u64`s

Widen to 65 bits so the sum can't overflow, shift, then truncate back.
-/

namespace Avg

/-- Spec: the true (floor) average. Widen to 65 bits so the sum can't overflow. -/
def avgSpec (a b : BitVec 64) : BitVec 64 :=
  ((a.setWidth 65 + b.setWidth 65) >>> 1).setWidth 64

/-- Bridge theorem: the bitvector spec is plain natural-number averaging. -/
theorem avgSpec_toNat (a b : BitVec 64) :
    (avgSpec a b).toNat = (a.toNat + b.toNat) / 2 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [avgSpec, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add,
    Nat.shiftRight_eq_div_pow]
  omega

end Avg
