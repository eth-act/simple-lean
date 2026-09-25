/-!
# Specification: the floor average of two `u64`s

`IsAvg a b r` says `r` is the floor average of `a` and `b`: `r = (a + b) / 2`, computed on
unbounded natural numbers, so the sum cannot overflow. It is a relation, not an algorithm,
so there is no widening or bit trick to trust here; implementations prove they produce such
an `r`.

`IsAvg.exists` and `IsAvg.unique` show it pins down exactly one result for every input,
so "satisfies `IsAvg`" is as strong as "equals the average".

## What a reviewer must read

This file, plus the *statements* (not proofs) of the end-to-end theorems, which say how
each implementation's inputs and outputs map onto `IsAvg`:

* `aeneas/AvgAeneas/Proofs.lean`: `rust_avg_correct`
* `riscv/AvgRiscv/Proofs.lean`: `avgProgram_spec` (and `avgProgram_correct`)

Everything else, including `algo/` and every proof body, is checked by Lean.
-/

namespace Avg

/-- `r` is the floor average of `a` and `b`, computed over `ℕ` (no overflow). -/
def IsAvg (a b r : BitVec 64) : Prop :=
  r.toNat = (a.toNat + b.toNat) / 2

instance (a b r : BitVec 64) : Decidable (IsAvg a b r) :=
  inferInstanceAs (Decidable (_ = _))

/-- Equivalent form without division: `2r ≤ a + b < 2r + 2`. -/
theorem IsAvg.iff_le {a b r : BitVec 64} :
    IsAvg a b r ↔ 2 * r.toNat ≤ a.toNat + b.toNat ∧ a.toNat + b.toNat < 2 * r.toNat + 2 := by
  unfold IsAvg; omega

/-- At most one result satisfies the spec. -/
theorem IsAvg.unique {a b r r' : BitVec 64} (h : IsAvg a b r) (h' : IsAvg a b r') : r = r' :=
  BitVec.eq_of_toNat_eq (h.trans h'.symm)

/-- Some result satisfies the spec: the average of two `u64`s always fits in a `u64`. -/
theorem IsAvg.exists (a b : BitVec 64) : ∃ r, IsAvg a b r := by
  refine ⟨BitVec.ofNat 64 ((a.toNat + b.toNat) / 2), ?_⟩
  have ha := a.isLt
  have hb := b.isLt
  unfold IsAvg
  rw [BitVec.toNat_ofNat]
  omega

/-! Sanity checks: the spec says what we mean, including where `u64` addition would overflow. -/

example : IsAvg 3 4 3 := by decide                       -- rounds down
example : ¬ IsAvg 3 4 4 := by decide
example : IsAvg 0x8000000000000000#64 0x8000000000000000#64 0x8000000000000000#64 := by decide
example : ¬ IsAvg 0x8000000000000000#64 0x8000000000000000#64 0#64 := by decide  -- wrapped sum
example : IsAvg 0xffffffffffffffff#64 0xffffffffffffffff#64 0xffffffffffffffff#64 := by decide

end Avg
