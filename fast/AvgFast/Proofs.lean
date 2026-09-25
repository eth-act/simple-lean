import Std.Tactic.BVDecide
import AvgSpec
import AvgFast.Impl

/-!
# `avgFast` meets the spec
-/

namespace Avg

/-- The optimised version is exactly the spec, for all 2^128 inputs. -/
theorem avgFast_eq_spec (a b : BitVec 64) : avgFast a b = avgSpec a b := by
  unfold avgFast avgSpec
  bv_decide

/-- Corollary: `avgFast` computes the natural-number average. -/
theorem avgFast_toNat (a b : BitVec 64) :
    (avgFast a b).toNat = (a.toNat + b.toNat) / 2 := by
  rw [avgFast_eq_spec, avgSpec_toNat]

/-- `(a &&& b) + ((a ^^^ b) >>> 1)` never carries out of 64 bits. -/
theorem avgFast_noOverflow (a b : BitVec 64) :
    (a &&& b).toNat + ((a ^^^ b) >>> 1).toNat ≤ 2 ^ 64 - 1 := by
  have h : BitVec.uaddOverflow (a &&& b) ((a ^^^ b) >>> 1) = false := by bv_decide
  simp only [BitVec.uaddOverflow, decide_eq_false_iff_not, Nat.not_le] at h
  omega

end Avg
