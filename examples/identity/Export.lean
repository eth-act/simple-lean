import Identity
import AssemblyX86

/-- A one-argument declaration tied to the exact verified identity program. -/
def Identity.exportFunction : AssemblyExport.Function Program
    (fun signature program => signature = .u64_1 ∧ Identity.Correct program) where
  symbol := "identity_u64"
  signature := .u64_1
  program := Identity.identityProgram
  correct := ⟨rfl, Identity.identityProgram_correct⟩

def main : IO Unit :=
  AssemblyExport.run (AssemblyX86.emit Identity.exportFunction)
