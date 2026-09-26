import AvgRiscv

namespace AvgRiscv

open RiscvZkvm.Rv64

/-- The two-argument ABI and full value, return and arbitrary-frame specification
for the exact instruction list supplied to the exporter. -/
def exportContract (signature : AssemblyExport.Signature) (program : List Instr) : Prop :=
  signature = .u64_2 ∧
  ∀ base a b vOld ra : Word,
    cpsTripleWithin 5 base (ra &&& ~~~1) (CodeReq.ofProg base program)
      ((.x10 ↦ᵣ a) ** (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ vOld) ** (.x1 ↦ᵣ ra))
      (fun h => ∃ r t, Avg.IsAvg a b r ∧
        ((.x10 ↦ᵣ r) ** (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ t) ** (.x1 ↦ᵣ ra)) h)

/-- Export permission is the existing composable correctness theorem, not a marker. -/
def exportFunction : AssemblyExport.Function (List Instr) exportContract where
  symbol := "avg"
  signature := .u64_2
  program := avgProgram
  correct := ⟨rfl, avgProgram_spec⟩

end AvgRiscv

def main : IO Unit :=
  AssemblyExport.run (AssemblyRiscv.emit AvgRiscv.exportFunction)
