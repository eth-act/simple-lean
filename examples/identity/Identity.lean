import Kraken.X64.Parser
import Kraken.X64.OmniSemantics

namespace Identity

open Kraken.X64.Parser

def identityProgram : Program := parse("
  movq %rdi, %rax
  ret
")

/-- Identity result, return address, popped stack pointer, and the complete frame.
The mapped return slot is ordinary memory, as required by Kraken's load semantics. -/
def Correct (program : Program) : Prop :=
  ∀ [layout : Layout] (s : MachineData) (ra : BitVec 64),
    Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofNat ra.toNat) →
    straightlineStep (layout program) (s, layout.start) (fun s' =>
      s'.1.regs.rax.toBitVec = s.regs.rdi.toBitVec ∧
      s'.2.toBitVec = ra ∧
      s'.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
      s'.1.dmem = s.dmem ∧ s'.1.zmms = s.zmms ∧ s'.1.status = s.status ∧
      (∀ r, r ≠ .rax → r ≠ .rsp → s'.1.regs.get64 r = s.regs.get64 r))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem identityProgram_correct : Correct identityProgram := by
  intro layout s ra hret
  unfold straightlineStep Executable.straightline
  rw [Kraken.Executable.directivesFromStart]
  simp only [identityProgram]
  simp [List.mapIdx, List.mapIdx.go, Directives.interp, Directive.interp, Instr.interp,
    Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get,
    Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
    MachineData.load, Effects.All, hret]
  intro r hax hsp
  cases r <;> simp_all

end Identity
