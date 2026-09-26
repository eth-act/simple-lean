import Std.Tactic.BVDecide
import AvgSpec
import AvgAlgo.Proofs
import AvgX86.Impl

/-!
# The x86-64 `avg` meets the spec

## Main results (these statements, plus `IsAvg`, are what a reviewer must read)

* `avgProgram_correct`: from any live state whose return address `[rsp]` is canonical,
  running the 6 instructions of `avgProgram` (x86lean's `run`) ends in a live state with
  `IsAvg rdi rsi rax`, `rip` = the return address, `rsp` popped by 8, and **every other
  general-purpose register, memory, the vector registers and the segment bases
  unchanged**. Only `rax`, `rsi`, `rsp`, `rip`, the flags and the undefined-bit oracle
  cursor may differ. `rsi` and the flags are caller-saved in the System V ABI.
* `avgProgram_toNat`: the result as `rax = ⌊(rdi + rsi) / 2⌋`.

Trusted here: x86lean's `step` (hand-written, differentially tested against ACL2 x86isa,
not proved against it), and the transcription of rustc's bytes into `avgProgram`
(x86lean has no decoder yet; `scripts/check-asm.py` compares against objdump). See TODO.md.
-/

namespace AvgX86

open X86

/-- After the body, `rax` holds `avgFast rdi rsi` (with operands in x86's order), and
the body touched only `rax`, `rsi`, flags, `rip` and the oracle. -/
theorem avgBody_run (s : Cpu) (h : Live s) :
    let s' := run avgBody s
    s'.regs.get .rax = (s.regs.get .rsi &&& s.regs.get .rdi) +
        ((s.regs.get .rsi ^^^ s.regs.get .rdi) >>> 1) ∧
      Live s' ∧
      s'.rip = s.rip + 15 ∧
      s'.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → s'.regs.get r = s.regs.get r) := by
  simp only [avgBody, run_cons, run_nil]
  rw [step_mov_reg_reg .q .rax .rsi h]
  rw [step_and_reg_reg .q .rax .rdi (by simpa [Live] using h)]
  rw [step_xor_reg_reg .q .rsi .rdi (by simpa [Live] using h)]
  rw [step_shift_reg_nonzero .shr .q .rsi 1 (by simpa [Live] using h) (by decide)]
  rw [step_add_reg_reg .q .rax .rsi (by simpa [Live] using h)]
  refine ⟨?_, by simpa [Live] using h, ?_, rfl, ?_⟩
  · simp only [Cpu.getReg, Value.writeView, Value.trunc, Flags.addResult, Flags.shiftCount,
      Size.mask]
    simp
    generalize s.regs.get .rsi = b
    generalize s.regs.get .rdi = a
    simp only [Val] at *
    bv_decide
  · simp only [BitVec.add_assoc]; rfl
  · intro r hax hsi
    cases r <;> simp_all [Regs.get, Regs.set]

/-- **Main theorem.** The whole function, including `ret`. -/
theorem avgProgram_correct (s : Cpu) (h : Live s)
    (hret : canonical (s.readMem .q (s.regs.get .rsp)) = true) :
    let s' := run avgProgram s
    Avg.IsAvg (s.regs.get .rdi) (s.regs.get .rsi) (s'.regs.get .rax) ∧
      Live s' ∧
      s'.rip = s.readMem .q (s.regs.get .rsp) ∧
      s'.regs.get .rsp = s.regs.get .rsp + 8 ∧
      s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.fsBase = s.fsBase ∧ s'.gsBase = s.gsBase ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rsp → s'.regs.get r = s.regs.get r) := by
  intro s'
  obtain ⟨hval, hlive, -, hmem, hregs⟩ := avgBody_run s h
  -- the body leaves memory and `rsp` alone, so `ret` pops the caller's return address
  have hrsp : (run avgBody s).regs.get .rsp = s.regs.get .rsp := hregs .rsp (by decide) (by decide)
  have hret' : canonical ((run avgBody s).readMem .q ((run avgBody s).regs.get .rsp)) = true := by
    simpa [Cpu.readMem, hmem, hrsp] using hret
  have hs' : s' = { (run avgBody s).setReg .q .rsp ((run avgBody s).regs.get .rsp + 8) with
      rip := (run avgBody s).readMem .q ((run avgBody s).regs.get .rsp) } := by
    simp only [s', avgProgram, run, List.foldl_append]
    exact step_ret_taken hlive hret'
  -- the body ran on `xmm`/segment bases through characterization equations that never
  -- name them, so they are unchanged
  have hbody : (run avgBody s).xmm = s.xmm ∧ (run avgBody s).fsBase = s.fsBase ∧
      (run avgBody s).gsBase = s.gsBase := by
    simp only [avgBody, run_cons, run_nil]
    rw [step_mov_reg_reg .q .rax .rsi h]
    rw [step_and_reg_reg .q .rax .rdi (by simpa [Live] using h)]
    rw [step_xor_reg_reg .q .rsi .rdi (by simpa [Live] using h)]
    rw [step_shift_reg_nonzero .shr .q .rsi 1 (by simpa [Live] using h) (by decide)]
    rw [step_add_reg_reg .q .rax .rsi (by simpa [Live] using h)]
    exact ⟨rfl, rfl, rfl⟩
  rw [hs']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rax is untouched by `ret`; the value is `avgFast` with operands swapped
    simp only [Cpu.setReg, Value.writeView]
    rw [Regs.get_set_ne _ _ _ _ (by decide), hval, BitVec.and_comm, BitVec.xor_comm]
    exact Avg.avgFast_isAvg _ _
  · simpa [Live, Cpu.setReg] using hlive
  · simp [Cpu.readMem, hmem, hrsp]
  · simp [Cpu.setReg, Value.writeView, hrsp]
  · simp [Cpu.setReg, hmem]
  · simp [Cpu.setReg, hbody.1]
  · simp [Cpu.setReg, hbody.2.1]
  · simp [Cpu.setReg, hbody.2.2]
  · intro r hax hsi hsp
    simp only [Cpu.setReg, Value.writeView]
    rw [Regs.get_set_ne _ _ _ _ (Ne.symm hsp)]
    exact hregs r hax hsi

/-- Plain-arithmetic form: `rax = ⌊(rdi + rsi) / 2⌋`. -/
theorem avgProgram_toNat (s : Cpu) (h : Live s)
    (hret : canonical (s.readMem .q (s.regs.get .rsp)) = true) :
    ((run avgProgram s).regs.get .rax).toNat =
      ((s.regs.get .rdi).toNat + (s.regs.get .rsi).toNat) / 2 :=
  (avgProgram_correct s h hret).1

end AvgX86
