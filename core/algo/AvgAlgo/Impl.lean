/-!
# Average algorithms (definitions only)

Proofs: `AvgAlgo.Proofs` (`avgWide` and `avgFast` meet the spec `IsAvg`) and
`AvgAlgo.Overflow` (`avgOverflow` doesn't). The `bv_decide` counterexample demo is the test
`AvgAlgoTest.Overflow`.

`avgWide` is the obvious correct algorithm: widen to 65 bits so the sum can't overflow.
`avgFast` stays in 64 bits using `a + b = 2·(a &&& b) + (a ^^^ b)`: shared bits count twice,
differing bits once. So `(a + b) / 2 = (a &&& b) + (a ^^^ b) / 2`, and neither term overflows.
-/

namespace Avg

/-- Widening: add in 65 bits, halve, truncate back. Correct, but needs a wider register. -/
def avgWide (a b : BitVec 64) : BitVec 64 :=
  ((a.setWidth 65 + b.setWidth 65) >>> 1).setWidth 64

/-- Optimised: stays in 64 bits, no widening needed. -/
def avgFast (a b : BitVec 64) : BitVec 64 :=
  (a &&& b) + ((a ^^^ b) >>> 1)

/-- Overflowing: `(a + b) / 2` in 64 bits. The sum wraps when `a + b ≥ 2^64`, so the result is wrong. -/
def avgOverflow (a b : BitVec 64) : BitVec 64 := (a + b) >>> 1

end Avg
