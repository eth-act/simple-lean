import AvgX86
import AssemblyX86

/-- The checked two-argument declaration refers to the complete result/return/frame contract. -/
def AvgX86.exportFunction : AssemblyExport.Function Program
    (fun signature program => signature = .u64_2 ∧ AvgX86.Correct program) where
  symbol := "avg"
  signature := .u64_2
  program := AvgX86.avgProgram
  correct := ⟨rfl, AvgX86.avgProgram_correct⟩

def main : IO Unit :=
  AssemblyExport.run (AssemblyX86.emit AvgX86.exportFunction)
