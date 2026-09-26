import AvgSpec
import AvgAlgo.Proofs
import AvgRiscv.Impl
import RiscvZkvm.Rv64.Logic

/-!
# The RV64IM `avg` meets the spec

## Main results (these statements, plus `IsAvg`, are what a reviewer must read)

* `avgProgram_spec`: separation-logic triple. From any state holding `a0 = a`, `a1 = b`,
  `a2`, `ra`, running at `base` with `avgProgram` loaded, the code reaches `ra &&& ~1`
  within 5 steps with `IsAvg a b a0`, `a1` and `ra` unchanged, `a2` clobbered, and
  **everything else (other registers, memory, I/O) untouched**: `cpsTripleWithin`
  quantifies over every frame `R` disjoint from those four registers. This is the
  statement a caller composes with.
* `avgProgram_correct` / `avgProgram_toNat`: the same result on a concrete machine
  state: exactly 5 `stepN` steps, no trap, `IsAvg a b a0`, pc = `ra &&& ~1`. Easier to
  read, but says nothing about the rest of the state; use `avgProgram_spec` for that.

`stepN` is riscv-zkvm's hand-written RV64IM model. Its per-instruction agreement with
the Sail RISC-V spec is `RiscvZkvm.Rv64.SailEquiv` (every instruction used here is
`simulable`); lifting these theorems to a Sail-level statement is future work (TODO.md).
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
(5 steps, no trap) to the caller's `ra` with the floor average of `a` and `b` in `a0`
(`IsAvg`, from the trusted spec). -/
theorem avgProgram_correct (s : MachineState) (base a b : Word)
    (hcode : ProgramAt s.code base avgProgram) (hpc : s.pc = base)
    (ha : s.getReg .x10 = a) (hb : s.getReg .x11 = b) :
    ∃ s', stepN 5 s = some s' ∧
      Avg.IsAvg a b (s'.getReg .x10) ∧
      s'.pc = s.getReg .x1 &&& ~~~1#64 := by
  obtain ⟨s', hrun, hval, hret⟩ := avgProgram_run s base hcode hpc
  refine ⟨s', hrun, ?_, hret⟩
  -- The code computes `(b & a) + ((b ^ a) >> 1)`, i.e. `avgFast` with operands swapped.
  rw [hval, ha, hb, BitVec.and_comm, BitVec.xor_comm]
  exact Avg.avgFast_isAvg a b

/-- Plain-arithmetic form: `a0 = ⌊(a + b) / 2⌋`. -/
theorem avgProgram_toNat (s : MachineState) (base a b : Word)
    (hcode : ProgramAt s.code base avgProgram) (hpc : s.pc = base)
    (ha : s.getReg .x10 = a) (hb : s.getReg .x11 = b) :
    ∃ s', stepN 5 s = some s' ∧ (s'.getReg .x10).toNat = (a.toNat + b.toNat) / 2 := by
  obtain ⟨s', hrun, hval, -⟩ := avgProgram_correct s base a b hcode hpc ha hb
  exact ⟨s', hrun, hval⟩

/-! ## Separation-logic spec (framing) -/

/-- The block as a triple, built from riscv-zkvm's per-instruction specs by `runBlock`.
The postcondition is the raw formula; `avgProgram_spec` restates it through `IsAvg`. -/
theorem avgProgram_triple (base a b vOld ra : Word) :
    cpsTripleWithin 5 base (ra &&& ~~~1) (CodeReq.ofProg base avgProgram)
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ vOld) ** (.x1 ↦ᵣ ra))
      ((.x10 ↦ᵣ ((b &&& a) + ((b ^^^ a) >>> (1 : BitVec 6).toNat))) ** (.x11 ↦ᵣ b) **
        (.x12 ↦ᵣ (b &&& a)) ** (.x1 ↦ᵣ ra)) := by
  have hcr : CodeReq.ofProg base avgProgram =
      (CodeReq.singleton base (.AND .x12 .x11 .x10)).union
       ((CodeReq.singleton (base + 4) (.XOR .x10 .x11 .x10)).union
       ((CodeReq.singleton (base + 4 + 4) (.SRLI .x10 .x10 1)).union
       ((CodeReq.singleton (base + 4 + 4 + 4) (.ADD .x10 .x12 .x10)).union
        (CodeReq.singleton (base + 4 + 4 + 4 + 4) (.JALR .x0 .x1 0))))) := by
    simp only [avgProgram, CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  rw [hcr]
  have s1 := generic_3reg_spec_within (.AND .x12 .x11 .x10) .x11 .x10 .x12 b a vOld (b &&& a)
    base (by decide)
    (by intro s _ h1 h2; simp [execInstrBr, h1, h2])
    (by intro s hf; exact step_non_ecall_non_mem hf (by nofun) (by nofun) (by rfl))
  have s2 := generic_2reg_spec_within (.XOR .x10 .x11 .x10) .x11 .x10 b a (b ^^^ a)
    (base + 4) (by decide)
    (by intro s _ h1 h2; simp [execInstrBr, h1, h2])
    (by intro s hf; exact step_non_ecall_non_mem hf (by nofun) (by nofun) (by rfl))
  have s3 := srli_spec_gen_same_within .x10 (b ^^^ a) 1 (base + 4 + 4) (by decide)
  have s4 := add_spec_rd_eq_rs2_within .x10 .x12 (b &&& a) ((b ^^^ a) >>> (1 : BitVec 6).toNat)
    (base + 4 + 4 + 4) (by decide)
  have s5 := jalr_x0_spec_gen_within .x1 ra 0 (base + 4 + 4 + 4 + 4)
  have h0 : ra + signExtend12 0 = ra := by simp [signExtend12]
  rw [h0] at s5
  runBlock s1 s2 s3 s4 s5

/-- **Main theorem (composable).** Running `avgProgram` at `base` with `a0 = a`, `a1 = b`
returns to `ra` within 5 steps with the floor average of `a` and `b` in `a0` (`IsAvg`,
from the trusted spec), `a1`/`ra` unchanged and `a2` clobbered. `cpsTripleWithin` holds
for every frame, so all other registers, memory and I/O are preserved. -/
theorem avgProgram_spec (base a b vOld ra : Word) :
    cpsTripleWithin 5 base (ra &&& ~~~1) (CodeReq.ofProg base avgProgram)
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ vOld) ** (.x1 ↦ᵣ ra))
      (fun h => ∃ r t, Avg.IsAvg a b r ∧
        ((.x10 ↦ᵣ r) ** (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ t) ** (.x1 ↦ᵣ ra)) h) :=
  cpsTripleWithin_weaken (fun _ h => h)
    (fun _ hq => ⟨_, _, by
      have := Avg.avgFast_isAvg a b
      simp only [Avg.avgFast] at this
      rw [BitVec.and_comm b a, BitVec.xor_comm b a]; exact this, hq⟩)
    (avgProgram_triple base a b vOld ra)

end AvgRiscv
