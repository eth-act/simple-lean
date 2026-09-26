import AvgSpec
import AvgAlgo.Impl

/-!
# The overflowing average does not meet the spec

`(a + b) / 2` overflows when `a + b ≥ 2^64`, the bug that broke binary search
in the Java standard library for nearly a decade.
-/

namespace Avg

/-- A concrete witness: `2^63 + 2^63` wraps to `0`, so `avgOverflow` returns `0`,
while the true average is `2^63`. -/
theorem avgOverflow_not_isAvg : ∃ a b : BitVec 64, ¬ IsAvg a b (avgOverflow a b) :=
  ⟨0x8000000000000000#64, 0x8000000000000000#64, by decide⟩

end Avg
