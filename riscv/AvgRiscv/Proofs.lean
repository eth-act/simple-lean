import AvgSpec
import AvgFast.Proofs
import AvgRiscv.Program

/-!
# The RV64IM `avg` meets the spec

Load `avgProgram` at `base`, start with `pc = base`, `a0 = a`, `a1 = b`. Then after
exactly 5 steps of riscv-zkvm's `stepN`, the machine has returned to `ra` and `a0`
holds `avgSpec a b`. Nothing can trap: the program has no memory access and no syscall.

`stepN` is riscv-zkvm's hand-written RV64IM model. Its per-instruction agreement with
the Sail RISC-V spec is `RiscvZkvm.Rv64.SailEquiv` (every instruction used here is
`simulable`); lifting this theorem to a Sail-level statement is future work (TODO.md).
-/

namespace AvgRiscv

open RiscvZkvm.Rv64

/-- One `stepN` step of a non-memory, non-syscall instruction just executes it. -/
private theorem stepN_one_plain {s : MachineState} {i : Instr} (h : s.code s.pc = some i)
    (hne : i ≠ .ECALL) (hnb : i ≠ .EBREAK) (hnm : i.isMemAccess = false) :
    stepN 1 s = some (execInstrBr s i) := by
  rw [stepN_one]; exact step_non_ecall_non_mem h hne hnb hnm

private theorem pc_setPC {s : MachineState} {v : Word} : (s.setPC v).pc = v := rfl

private theorem getReg_setReg_eq {t : MachineState} {r : Reg} {v : Word} (h : r ≠ .x0) :
    (t.setReg r v).getReg r = v := MachineState.getReg_setReg_eq h

private theorem getReg_setReg_ne {t : MachineState} {r r' : Reg} {v : Word} (h : r ≠ r') :
    (t.setReg r v).getReg r' = t.getReg r' := MachineState.getReg_setReg_ne _ _ _ _ h

/-- Running the 5 instructions: `a0` gets the fast formula and control returns to `ra`. -/
theorem avgProgram_run (s : MachineState) (base : Word)
    (hcode : ProgramAt s.code base avgProgram) (hpc : s.pc = base) :
    ∃ s', stepN 5 s = some s' ∧
      s'.getReg .x10 =
        (s.getReg .x11 &&& s.getReg .x10) + ((s.getReg .x11 ^^^ s.getReg .x10) >>> 1) ∧
      s'.pc = s.getReg .x1 &&& ~~~1#64 := by
  have fetch : ∀ k (hk : k < avgProgram.length) i, avgProgram[k]? = some i →
      s.code (base + BitVec.ofNat 64 (4 * k)) = some i :=
    fun k hk i hi => (hcode.get hk).trans hi
  let s1 := execInstrBr s (.AND .x12 .x11 .x10)
  let s2 := execInstrBr s1 (.XOR .x10 .x11 .x10)
  let s3 := execInstrBr s2 (.SRLI .x10 .x10 1)
  let s4 := execInstrBr s3 (.ADD .x10 .x12 .x10)
  let s5 := execInstrBr s4 (.JALR .x0 .x1 0)
  -- the pc walks through the program 4 bytes at a time
  have p1 : s1.pc = base + BitVec.ofNat 64 (4 * 1) := by simp [s1, execInstrBr, pc_setPC, hpc]
  have p2 : s2.pc = base + BitVec.ofNat 64 (4 * 2) := by simp [s2, execInstrBr, pc_setPC, p1]; bv_omega
  have p3 : s3.pc = base + BitVec.ofNat 64 (4 * 3) := by simp [s3, execInstrBr, pc_setPC, p2]; bv_omega
  have p4 : s4.pc = base + BitVec.ofNat 64 (4 * 4) := by simp [s4, execInstrBr, pc_setPC, p3]; bv_omega
  have c : ∀ t : MachineState, ∀ i, (execInstrBr t i).code = t.code := fun _ _ => code_execInstrBr
  -- each step fetches the next instruction and executes it
  have h1 : stepN 1 s = some s1 := stepN_one_plain
    (by rw [hpc]; simpa using fetch 0 (by decide) _ rfl) (by decide) (by decide) (by decide)
  have h2 : stepN 1 s1 = some s2 := stepN_one_plain
    (by rw [p1, c]; exact fetch 1 (by decide) _ rfl) (by decide) (by decide) (by decide)
  have h3 : stepN 1 s2 = some s3 := stepN_one_plain
    (by rw [p2, c, c]; exact fetch 2 (by decide) _ rfl) (by decide) (by decide) (by decide)
  have h4 : stepN 1 s3 = some s4 := stepN_one_plain
    (by rw [p3, c, c, c]; exact fetch 3 (by decide) _ rfl) (by decide) (by decide) (by decide)
  have h5 : stepN 1 s4 = some s5 := stepN_one_plain
    (by rw [p4, c, c, c, c]; exact fetch 4 (by decide) _ rfl) (by decide) (by decide) (by decide)
  refine ⟨s5, stepN_add_eq (stepN_add_eq (stepN_add_eq (stepN_add_eq h1 h2) h3) h4) h5, ?_, ?_⟩
  · simp only [s5, s4, s3, s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_eq (r := .x10) (by decide), getReg_setReg_eq (r := .x12) (by decide),
      getReg_setReg_ne (r := .x12) (r' := .x10) (by decide),
      getReg_setReg_ne (r := .x12) (r' := .x11) (by decide),
      getReg_setReg_ne (r := .x10) (r' := .x12) (by decide)]
    rfl
  · simp only [s5, s4, s3, s2, s1, execInstrBr, pc_setPC, signExtend12, MachineState.getReg_setPC,
      getReg_setReg_ne (r := .x10) (r' := .x1) (by decide),
      getReg_setReg_ne (r := .x12) (r' := .x1) (by decide)]
    bv_decide

/-- **Main theorem.** With `a` in `a0` and `b` in `a1`, the machine code returns
(5 steps, no trap) to the caller's `ra` with `avgSpec a b` in `a0`. -/
theorem avgProgram_correct (s : MachineState) (base a b : Word)
    (hcode : ProgramAt s.code base avgProgram) (hpc : s.pc = base)
    (ha : s.getReg .x10 = a) (hb : s.getReg .x11 = b) :
    ∃ s', stepN 5 s = some s' ∧
      s'.getReg .x10 = Avg.avgSpec a b ∧
      s'.pc = s.getReg .x1 &&& ~~~1#64 := by
  obtain ⟨s', hrun, hval, hret⟩ := avgProgram_run s base hcode hpc
  refine ⟨s', hrun, ?_, hret⟩
  -- The code computes `(b & a) + ((b ^ a) >> 1)`, i.e. `avgFast` with operands swapped.
  rw [hval, ha, hb, BitVec.and_comm, BitVec.xor_comm]
  exact Avg.avgFast_eq_spec a b

/-- Plain-arithmetic form, via the spec's bridge theorem: `a0 = ⌊(a + b) / 2⌋`. -/
theorem avgProgram_toNat (s : MachineState) (base a b : Word)
    (hcode : ProgramAt s.code base avgProgram) (hpc : s.pc = base)
    (ha : s.getReg .x10 = a) (hb : s.getReg .x11 = b) :
    ∃ s', stepN 5 s = some s' ∧ (s'.getReg .x10).toNat = (a.toNat + b.toNat) / 2 := by
  obtain ⟨s', hrun, hval, -⟩ := avgProgram_correct s base a b hcode hpc ha hb
  exact ⟨s', hrun, by rw [hval, Avg.avgSpec_toNat]⟩

end AvgRiscv
