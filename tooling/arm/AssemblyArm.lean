import AssemblyExport
import Arm.Decode

namespace AssemblyArm

/-- `some false` is a supported data instruction; `some true` is a return.
Only 64-bit AND/EOR and ADD (shifted register), plus RET, are supported.
These classes have no PC-relative operands, relocations or memory effects.
Register operands are unrestricted except RET's register 31: the model reads it
as SP, unlike the architectural zero-register operand. ABI/frame obligations
and the value of the return address belong to the client's proof. -/
private def classify (word : BitVec 32) : Option Bool :=
  match decode_raw_inst word with
  | some (.DPR (.Logical_shifted_reg inst)) =>
      if inst.sf == 1 && inst.N == 0 && (inst.opc == 0 || inst.opc == 2) then
        some false
      else none
  | some (.DPR (.Add_sub_shifted_reg inst)) =>
      if inst.sf == 1 && inst.op == 0 && inst.S == 0 && inst.shift != 3 then
        some false
      else none
  | some (.BR (.Uncond_branch_reg inst)) =>
      if inst.opc == 2 && inst.op2 == 31 && inst.op3 == 0 && inst.op4 == 0 &&
          inst.Rn != 31 then
        some true
      else none
  | _ => none

private def emitWord (word : BitVec 32) : String :=
  let bytes := (List.range 4).map fun i => toString ((word.toNat >>> (8 * i)) % 256)
  "  .byte " ++ String.intercalate ", " bytes ++ "\n"

private def emitBody : List (BitVec 32) → Nat → Except String (List String)
  | [], _ => .error "AArch64 leaf function must end with RET"
  | word :: rest, index => do
      let some returns := classify word
        | throw s!"unsupported or invalid AArch64 instruction at index {index}: 0x{word.toHex}"
      if returns then
        if !rest.isEmpty then
          throw s!"AArch64 RET at index {index} is followed by code"
        return [emitWord word]
      let body ← emitBody rest (index + 1)
      return emitWord word :: body

/-- Emit the exact checked instruction words as little-endian GNU ELF assembly.
Unsupported encodings, missing returns and code after a return are rejected. -/
def emit {contract : AssemblyExport.Signature → List (BitVec 32) → Prop}
    (fn : AssemblyExport.Function (List (BitVec 32)) contract) :
    Except String AssemblyExport.Artifact := do
  let body ← emitBody fn.program 0
  AssemblyExport.render fn "aarch64-linux-gnu" (String.join body) "" 2 "%"

end AssemblyArm
