/-!
# Average implementations (definitions only)

Proofs live in `Avg.Proofs.Fast`; the naive version's counterexample in `AvgTest.Naive`.

`avgFast` uses `a + b = 2·(a &&& b) + (a ^^^ b)`: shared bits count twice, differing
bits once. So `(a + b) / 2 = (a &&& b) + (a ^^^ b) / 2`, and neither term can overflow.
-/

namespace Avg

/-- Optimised: stays in 64 bits, no widening needed. -/
def avgFast (a b : BitVec 64) : BitVec 64 :=
  (a &&& b) + ((a ^^^ b) >>> 1)

/-- Naive: `(a + b) / 2`. The sum wraps on overflow, so this is *wrong*. -/
def avgNaive (a b : BitVec 64) : BitVec 64 := (a + b) >>> 1

end Avg
