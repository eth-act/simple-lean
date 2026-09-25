import Std.Tactic.BVDecide
import Avg.Spec

/-!
# Optimised average

`a + b = 2·(a &&& b) + (a ^^^ b)`: shared bits count twice, differing bits once.
So `(a + b) / 2 = (a &&& b) + (a ^^^ b) / 2`, and neither term can overflow.
-/

namespace Avg

/-- Optimised: stays in 64 bits, no widening needed. -/
def avgFast (a b : BitVec 64) : BitVec 64 :=
  (a &&& b) + ((a ^^^ b) >>> 1)

/-- The optimised version is exactly the spec, for all 2^128 inputs. -/
theorem avgFast_eq_spec (a b : BitVec 64) : avgFast a b = avgSpec a b := by
  unfold avgFast avgSpec
  bv_decide

/-- Corollary: `avgFast` computes the natural-number average. -/
theorem avgFast_toNat (a b : BitVec 64) :
    (avgFast a b).toNat = (a.toNat + b.toNat) / 2 := by
  rw [avgFast_eq_spec, avgSpec_toNat]

end Avg
