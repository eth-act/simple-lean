import Std.Tactic.BVDecide
import Avg.Spec
import Avg.Impl.Fast

/-!
# `bv_decide` rejects the naive average with a counterexample

Pins the exact message: if a Lean upgrade changes `bv_decide`'s output, update it here.
The theorem that `avgNaive` is wrong lives in `Avg.Proofs.Naive`.
-/

namespace Avg

/--
error: The prover found a counterexample, consider the following assignment:
a = 18446744073709551615#64
b = 18446744073709551615#64
-/
#guard_msgs in
theorem avgNaive_eq_spec (a b : BitVec 64) : avgNaive a b = avgSpec a b := by
  unfold avgNaive avgSpec
  bv_decide

end Avg
