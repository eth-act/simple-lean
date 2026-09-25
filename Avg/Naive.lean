import Std.Tactic.BVDecide
import Avg.Spec

/-!
# The naive average is wrong

`(a + b) / 2` overflows when `a + b ≥ 2^64` — the bug that broke binary search
in the Java standard library for nearly a decade.
-/

namespace Avg

/-- Naive: the sum wraps around on overflow. -/
def avgNaive (a b : BitVec 64) : BitVec 64 := (a + b) >>> 1

/--
error: The prover found a counterexample, consider the following assignment:
a = 18446744073709551615#64
b = 18446744073709551615#64
-/
#guard_msgs in
theorem avgNaive_eq_spec (a b : BitVec 64) : avgNaive a b = avgSpec a b := by
  unfold avgNaive avgSpec
  bv_decide

/-- A concrete witness: `2^63 + 2^63` wraps to `0`, so the naive average is `0`,
while the true average is `2^63`. -/
theorem avgNaive_ne_spec : ∃ a b : BitVec 64, avgNaive a b ≠ avgSpec a b :=
  ⟨0x8000000000000000#64, 0x8000000000000000#64, by decide⟩

end Avg
