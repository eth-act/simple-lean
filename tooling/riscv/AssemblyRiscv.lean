import AssemblyExport
import RiscvZkvm.Interpreter.Decode

namespace AssemblyRiscv

open RiscvZkvm.Rv64
open RiscvZkvm.Interpreter (decode)

private def regBits (r : Reg) : BitVec 5 := BitVec.ofNat 5 r.toNat

private def encodeR (funct3 : BitVec 3) (rd rs1 rs2 : Reg) : BitVec 32 :=
  0#7 ++ regBits rs2 ++ regBits rs1 ++ funct3 ++ regBits rd ++ 0x33#7

/-- Encode the supported RV64I instructions with their actual register and immediate fields.
Unsupported instructions fail rather than becoming a placeholder instruction. -/
def encodeInstr : Instr → Option (BitVec 32)
  | .AND rd rs1 rs2 => some (encodeR 7 rd rs1 rs2)
  | .XOR rd rs1 rs2 => some (encodeR 4 rd rs1 rs2)
  | .SRLI rd rs1 shamt =>
      some (0#6 ++ shamt ++ regBits rs1 ++ 5#3 ++ regBits rd ++ 0x13#7)
  | .ADD rd rs1 rs2 => some (encodeR 0 rd rs1 rs2)
  | .JALR rd rs1 offset =>
      some (offset ++ regBits rs1 ++ 0#3 ++ regBits rd ++ 0x67#7)
  | _ => none

/-- Encode a program, rejecting the entire program if any instruction is unsupported. -/
def encodeProgram : List Instr → Option (List (BitVec 32))
  | [] => some []
  | instr :: rest => do
      let word ← encodeInstr instr
      let words ← encodeProgram rest
      pure (word :: words)

/-- Successful checked encodings carry the decoder's exact agreement with the input.
The equality is checked for every new program, not assumed from a previous client. -/
def checkedEncodeProgram (program : List Instr) :
    Except String { words : List (BitVec 32) // words.map decode = program.map some } := do
  let words ← match encodeProgram program with
    | some words => pure words
    | none => throw "unsupported RISC-V instruction"
  if h : words.map decode = program.map some then
    return ⟨words, h⟩
  else
    throw "RISC-V encoding does not decode to the input program"

/-- The four bytes of a word, in the order emitted into the ELF text section. -/
def wordBytesLE (word : BitVec 32) : List (BitVec 8) :=
  [word.extractLsb' 0 8, word.extractLsb' 8 8,
   word.extractLsb' 16 8, word.extractLsb' 24 8]

/-- Reassemble complete little-endian words, rejecting a truncated final word. -/
def wordsFromBytesLE : List (BitVec 8) → Option (List (BitVec 32))
  | [] => some []
  | a :: b :: c :: d :: rest => do
      let words ← wordsFromBytesLE rest
      pure ((d ++ c ++ b ++ a) :: words)
  | _ => none

/-- Only straight-line integer leaf bodies with one final ABI return are supported. -/
private def checkLeafProgram : List Instr → Except String Unit
  | [] => .error "RISC-V function must end with JALR x0 x1 0"
  | .JALR rd rs1 offset :: rest =>
      if rd = .x0 ∧ rs1 = .x1 ∧ offset = 0 then
        if rest.isEmpty then .ok ()
        else .error "RISC-V return must be the final instruction"
      else
        .error "only the final RISC-V return JALR x0 x1 0 is supported"
  | .AND _ _ _ :: rest
  | .XOR _ _ _ :: rest
  | .SRLI _ _ _ :: rest
  | .ADD _ _ _ :: rest => checkLeafProgram rest
  | _ => .error "unsupported RISC-V leaf instruction"

/-- Export a client-proved leaf function as little-endian RV64 instruction bytes.
The client contract is responsible for value, return and frame correctness. -/
def emit {contract : AssemblyExport.Signature → List Instr → Prop}
    (fn : AssemblyExport.Function (List Instr) contract) : Except String AssemblyExport.Artifact := do
  checkLeafProgram fn.program
  let words ← checkedEncodeProgram fn.program
  let body := String.join (words.val.map fun word =>
    "  .byte " ++ String.intercalate ", " ((wordBytesLE word).map (fun byte => toString byte.toNat)) ++
      "\n")
  AssemblyExport.render fn "riscv64-linux-gnu" body

end AssemblyRiscv
