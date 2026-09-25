import Avg.Spec
import Avg.Impl.Fast

/-!
# The naive average does not meet the spec

`(a + b) / 2` overflows when `a + b ≥ 2^64`, the bug that broke binary search
in the Java standard library for nearly a decade.
-/

namespace Avg

/-- A concrete witness: `2^63 + 2^63` wraps to `0`, so the naive average is `0`,
while the true average is `2^63`. -/
theorem avgNaive_ne_spec : ∃ a b : BitVec 64, avgNaive a b ≠ avgSpec a b :=
  ⟨0x8000000000000000#64, 0x8000000000000000#64, by decide⟩

end Avg
