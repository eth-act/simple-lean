import Arm.Exec
import AvgSpec
import AvgAlgo.Proofs
import AvgArm.Impl

/-!
# The AArch64 `avg` meets the spec

## Main results (these statements, plus `IsAvg`, are what a reviewer must read)

* `avgProgram_correct`: from any error-free LNSym state whose program map holds the 4 words
  of `avgProgram` at `base` (`CodeAt`) and whose pc is `base`, running 4 steps (LNSym's
  `run 4`) ends in an error-free state with `IsAvg x0 x1 x0'`, pc = the caller's `x30`,
  and **every other state component unchanged**: memory, the program map, and every
  register (other GPRs incl. `sp`, all SIMD/FP registers, the NZCV flags). Only `x0`, `x8`,
  `x9` and the pc may differ. `x8`/`x9` are caller-saved temporaries in AAPCS64.
* `avgProgram_toNat`: the result as `x0' = ⌊(x0 + x1) / 2⌋`.
* `codeAt_loadAt`: `CodeAt` holds for the plain program map `loadAt base avgProgram`, at
  every `base`, so the hypothesis of `avgProgram_correct` is satisfiable.

`r (.GPR i) s` is register `xi` of `s` (`i = 31` is `sp`); `read_pc`/`read_err` are
`r .PC`/`r .ERR`. LNSym's `StateField` (GPRs, SIMD/FP registers, pc, NZCV, error) plus
`mem` and `program` is the entire LNSym state, so the frame clause covers all of it.

Trusted here: LNSym's `stepi` (hand-written from the Arm ARM; each implemented instruction
class is differentially tested against real AArch64 hardware by LNSym's cosim, not proved
against Arm's ASL spec). That includes its decoder `decode_raw_inst`, but nothing past it:
the proof starts from rustc's raw instruction words, and each step lemma below decodes its
word by kernel evaluation, so no bytes-to-instruction transcription is trusted. LNSym keeps
code in a separate `program` map, disjoint from data memory by construction (no
self-modifying code). See TODO.md.
-/

namespace AvgArm

open BitVec

/-! ## One step per instruction

Each lemma fetches the word at the pc, decodes it with `decode_raw_inst` (the final `rfl`
argument is checked by the kernel), and simplifies `exec_inst` with LNSym's own
`state_simp_rules`. The pc stays symbolic: LNSym's `#genStepEqTheorems`/`sym_n` automation
needs the program at concrete addresses, and `avg` must be correct wherever it is linked. -/

theorem step_eor (s : ArmState) (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some 0xca000028#32) :
    stepi s = w (.GPR 8) (r (.GPR 1) s ^^^ r (.GPR 0) s) (w .PC (read_pc s + 4#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true}) only [exec_inst, state_simp_rules, bitvec_rules,
    minimal_theory, Nat.reduceShiftLeft, BitVec.setWidth_eq]
  -- `x0, lsl #0`: the shift-by-zero sits under an instance simp won't rewrite through
  exact congrArg (fun v => w (.GPR 8) (_ ^^^ v) _) (BitVec.shiftLeft_zero _)

theorem step_and (s : ArmState) (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some 0x8a000029#32) :
    stepi s = w (.GPR 9) (r (.GPR 1) s &&& r (.GPR 0) s) (w .PC (read_pc s + 4#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true}) only [exec_inst, state_simp_rules, bitvec_rules,
    minimal_theory, Nat.reduceShiftLeft, BitVec.setWidth_eq]
  exact congrArg (fun v => w (.GPR 9) (_ &&& v) _) (BitVec.shiftLeft_zero _)

theorem step_add_lsr (s : ArmState) (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some 0x8b480520#32) :
    stepi s = w (.GPR 0) (r (.GPR 9) s + (r (.GPR 8) s >>> 1)) (w .PC (read_pc s + 4#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true}) only [exec_inst, state_simp_rules, bitvec_rules,
    minimal_theory, Nat.reduceShiftLeft, BitVec.setWidth_eq, BitVec.ushiftRight_eq]

theorem step_ret (s : ArmState) (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some 0xd65f03c0#32) :
    stepi s = w .PC (r (.GPR 30) s) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true}) only [exec_inst, state_simp_rules, bitvec_rules,
    minimal_theory]

/-! ## The whole function -/

/-- The exact final state: after `run 4`, the state is `s` with four register writes
(and the pc writes between them). -/
theorem avgProgram_run (s : ArmState) (base : BitVec 64) (hcode : CodeAt s base avgProgram)
    (hpc : read_pc s = base) (herr : read_err s = .None) :
    run 4 s =
      w .PC (r (.GPR 30) s)
        (w (.GPR 0) ((r (.GPR 1) s &&& r (.GPR 0) s) + ((r (.GPR 1) s ^^^ r (.GPR 0) s) >>> 1))
          (w .PC (base + 12#64)
            (w (.GPR 9) (r (.GPR 1) s &&& r (.GPR 0) s)
              (w .PC (base + 8#64)
                (w (.GPR 8) (r (.GPR 1) s ^^^ r (.GPR 0) s)
                  (w .PC (base + 4#64) s)))))) := by
  have herr' : r .ERR s = .None := herr
  let a := r (.GPR 0) s
  let b := r (.GPR 1) s
  let s1 := w (.GPR 8) (b ^^^ a) (w .PC (base + 4#64) s)
  let s2 := w (.GPR 9) (b &&& a) (w .PC (base + 8#64) s1)
  let s3 := w (.GPR 0) ((b &&& a) + ((b ^^^ a) >>> 1)) (w .PC (base + 12#64) s2)
  have h1 : stepi s = s1 := by
    rw [step_eor s herr (by simpa [hpc, avgProgram] using hcode 0 (by decide))]
    simp only [s1, a, b, hpc]
  have h2 : stepi s1 = s2 := by
    rw [step_and s1 (by simp (config := {decide := true}) [s1, state_simp_rules, herr'])
      (by simpa (config := {decide := true}) [s1, state_simp_rules, avgProgram] using
        hcode 1 (by decide))]
    simp (config := {decide := true}) only [s1, s2, a, b, state_simp_rules, minimal_theory,
      BitVec.add_assoc, BitVec.reduceAdd]
  have h3 : stepi s2 = s3 := by
    rw [step_add_lsr s2 (by simp (config := {decide := true}) [s1, s2, state_simp_rules, herr'])
      (by simpa (config := {decide := true}) [s1, s2, state_simp_rules, avgProgram] using
        hcode 2 (by decide))]
    simp (config := {decide := true}) only [s1, s2, s3, a, b, state_simp_rules, minimal_theory,
      BitVec.add_assoc, BitVec.reduceAdd]
  have h4 : stepi s3 = w .PC (r (.GPR 30) s) s3 := by
    rw [step_ret s3
      (by simp (config := {decide := true}) [s1, s2, s3, state_simp_rules, herr'])
      (by simpa (config := {decide := true}) [s1, s2, s3, state_simp_rules, avgProgram] using
        hcode 3 (by decide))]
    simp (config := {decide := true}) only [s1, s2, s3, state_simp_rules, minimal_theory]
  show stepi (stepi (stepi (stepi s))) = _
  rw [h1, h2, h3, h4]

/-- **Main theorem.** The whole function, including `ret`. -/
theorem avgProgram_correct (s : ArmState) (base : BitVec 64) (hcode : CodeAt s base avgProgram)
    (hpc : read_pc s = base) (herr : read_err s = .None) :
    let s' := run 4 s
    Avg.IsAvg (r (.GPR 0) s) (r (.GPR 1) s) (r (.GPR 0) s') ∧
      read_err s' = .None ∧
      read_pc s' = r (.GPR 30) s ∧
      s'.mem = s.mem ∧ s'.program = s.program ∧
      (∀ f, f ≠ .GPR 0 → f ≠ .GPR 8 → f ≠ .GPR 9 → f ≠ .PC → r f s' = r f s) := by
  intro s'
  simp only [s', avgProgram_run s base hcode hpc herr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [state_simp_rules, minimal_theory]
    rw [BitVec.and_comm, BitVec.xor_comm]
    exact Avg.avgFast_isAvg _ _
  · simp [state_simp_rules, show r .ERR s = .None from herr]
  · simp [state_simp_rules]
  · simp [state_simp_rules]
  · simp [state_simp_rules]
  · intro f h0 h8 h9 hpc'
    rw [r_of_w_different hpc', r_of_w_different h0, r_of_w_different hpc', r_of_w_different h9,
      r_of_w_different hpc', r_of_w_different h8, r_of_w_different hpc']

/-- Plain-arithmetic form: `x0' = ⌊(x0 + x1) / 2⌋`. -/
theorem avgProgram_toNat (s : ArmState) (base : BitVec 64) (hcode : CodeAt s base avgProgram)
    (hpc : read_pc s = base) (herr : read_err s = .None) :
    (r (.GPR 0) (run 4 s)).toNat = ((r (.GPR 0) s).toNat + (r (.GPR 1) s).toNat) / 2 :=
  (avgProgram_correct s base hcode hpc herr).1

/-- `CodeAt` is satisfiable: the plain program map `loadAt base avgProgram` holds the code
at `base`, for every `base`. -/
theorem codeAt_loadAt (s : ArmState) (base : BitVec 64)
    (h : s.program = loadAt base avgProgram) : CodeAt s base avgProgram := by
  intro k hk
  rw [h]
  simp only [avgProgram, List.length_cons, List.length_nil] at hk
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ => simp [loadAt, avgProgram, Map.find?]

end AvgArm
