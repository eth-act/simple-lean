import AvgSpec
import AvgAlgo.Proofs
import AvgX86.Impl

/-!
# Complete x86-64 correctness under Kraken

`avgProgram_correct` proves the average, return PC, popped stack pointer, and the
memory/vector/GPR frame. Only `rax`, `rsi`, `rsp`, PC and status flags may change.
Kraken's hand-written assembly semantics and the objdump binding are trusted.
The model does not include segment bases or canonical-address faults, and its
omnisemantics discharges access-request effects rather than modeling page permissions.
-/

namespace AvgX86

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The complete function, including the stack load and return. Undefined flag choices
are universally quantified by Kraken's `straightlineStep`. The stack slot must be mapped
ordinary memory; the semantics rejects non-memory loads. Instruction sizes and base are
arbitrary because this function does not observe instruction addresses. -/
theorem avgProgram_correct [layout : Layout] (s : MachineData) (ra : BitVec 64)
    (hret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofNat ra.toNat)) :
    straightlineStep (layout avgProgram) (s, layout.start) (fun s' =>
      Avg.IsAvg s.regs.rdi.toBitVec s.regs.rsi.toBitVec s'.1.regs.rax.toBitVec ∧
      s'.2.toBitVec = ra ∧
      s'.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
      s'.1.dmem = s.dmem ∧ s'.1.zmms = s.zmms ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rsp → s'.1.regs.get64 r = s.regs.get64 r)) := by
  unfold straightlineStep Executable.straightline
  rw [Kraken.Executable.directivesFromStart]
  simp only [avgProgram]
  simp [List.mapIdx, List.mapIdx.go, Directives.interp, Directive.interp, Instr.interp,
    Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get,
    Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
    MachineData.load, Effects.All, hret]
  constructor
  · simpa [Avg.avgFast, BitVec.add_comm, BitVec.and_comm, BitVec.xor_comm] using
      Avg.avgFast_isAvg s.regs.rdi.toBitVec s.regs.rsi.toBitVec
  · intro r hax hsi hsp
    cases r <;> simp_all

end AvgX86
