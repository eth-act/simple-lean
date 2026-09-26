import Std.Tactic.BVDecide
import AvgAlgo.Proofs
import AvgAlgo.Impl

/-!
# `bv_decide` rejects `avgOverflow` with a counterexample

Pins the exact message: if a Lean upgrade changes `bv_decide`'s output, update it here.
`bv_decide` needs a bitvector goal, so this compares against `avgWide` (proved to satisfy
`IsAvg` in `AvgAlgo.Proofs`). The theorem that `avgOverflow` fails the spec is in `AvgAlgo.Overflow`.
-/

namespace Avg

/--
error: The prover found a counterexample, consider the following assignment:
a = 18446744073709551615#64
b = 18446744073709551615#64
-/
#guard_msgs in
theorem avgOverflow_eq_wide (a b : BitVec 64) : avgOverflow a b = avgWide a b := by
  unfold avgOverflow avgWide
  bv_decide

end Avg
