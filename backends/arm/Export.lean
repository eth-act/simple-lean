import AvgArm
import AssemblyArm

namespace AvgArm

/-- The binary's C signature, result, return and complete frame contract.
Both the code-loading premise and execution length refer to the exported program. -/
def ExportContract (signature : AssemblyExport.Signature) (program : List (BitVec 32)) : Prop :=
  signature = .u64_2 ∧
    ∀ (s : ArmState) (base : BitVec 64), CodeAt s base program →
      read_pc s = base → read_err s = .None →
      let s' := run program.length s
      Avg.IsAvg (r (.GPR 0) s) (r (.GPR 1) s) (r (.GPR 0) s') ∧
        read_err s' = .None ∧
        read_pc s' = r (.GPR 30) s ∧
        s'.mem = s.mem ∧ s'.program = s.program ∧
        (∀ f, f ≠ .GPR 0 → f ≠ .GPR 8 → f ≠ .GPR 9 → f ≠ .PC → r f s' = r f s)

/-- The declaration is checked against the full machine-code correctness theorem. -/
def exportFunction : AssemblyExport.Function (List (BitVec 32)) ExportContract where
  symbol := "avg"
  signature := .u64_2
  program := avgProgram
  correct := ⟨rfl, fun s base hcode hpc herr => avgProgram_correct s base hcode hpc herr⟩

end AvgArm

/-- Export the proved declaration through the generic AArch64 adapter. -/
def main : IO Unit :=
  AssemblyExport.run (AssemblyArm.emit AvgArm.exportFunction)
