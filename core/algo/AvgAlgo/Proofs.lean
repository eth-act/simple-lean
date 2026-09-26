import Std.Tactic.BVDecide
import AvgSpec
import AvgAlgo.Impl

/-!
# `avgWide` and `avgFast` meet the spec

`avgWide` is proved against `IsAvg` by lifting to `ℕ` (`omega`). `avgFast` is proved equal
to `avgWide` for all 2^128 inputs by `bv_decide`, and inherits the spec from it.
-/

namespace Avg

/-- The widening algorithm computes the floor average. -/
theorem avgWide_isAvg (a b : BitVec 64) : IsAvg a b (avgWide a b) := by
  have ha := a.isLt
  have hb := b.isLt
  unfold IsAvg
  simp only [avgWide, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The optimised version equals the widening one, for all 2^128 inputs. -/
theorem avgFast_eq_wide (a b : BitVec 64) : avgFast a b = avgWide a b := by
  unfold avgFast avgWide
  bv_decide

/-- The optimised version computes the floor average. -/
theorem avgFast_isAvg (a b : BitVec 64) : IsAvg a b (avgFast a b) :=
  avgFast_eq_wide a b ▸ avgWide_isAvg a b

/-- `(a &&& b) + ((a ^^^ b) >>> 1)` never carries out of 64 bits. -/
theorem avgFast_noOverflow (a b : BitVec 64) :
    (a &&& b).toNat + ((a ^^^ b) >>> 1).toNat ≤ 2 ^ 64 - 1 := by
  have h : BitVec.uaddOverflow (a &&& b) ((a ^^^ b) >>> 1) = false := by bv_decide
  simp only [BitVec.uaddOverflow, decide_eq_false_iff_not, Nat.not_le] at h
  omega

end Avg
