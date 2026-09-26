#!/usr/bin/env python3
"""Check that rustc's machine code for `avg` is exactly the program each proof is about.

Each ISA proof under backends/ is about `avgProgram` in its `Impl.lean`:
an instruction list (RISC-V), parsed AT&T assembly (x86), or raw words (Arm).
This script ties that program to real compiler output:

  1. build impl/rust/ for the ISA's target (release),
  2. disassemble the `avg` symbol with objdump,
  3. compare instructions, normalised AT&T assembly, or raw words respectively.

Trusted here: rustc, objdump, this script, its RISC-V mapping and x86 normalisation.
Kraken parses assembly, not binary bytes. Arm decoding happens inside the Lean proof;
each model's ISA faithfulness remains trusted.

rustc is pinned (RUST_TOOLCHAIN): codegen can change between versions and each proof is
about one exact instruction sequence. Bumping it may require updating the Impl files.

Usage: scripts/check-asm.py [riscv|x86|arm ...]   (default: all; run from anywhere)
Needs: rustup with RUST_TOOLCHAIN and each ISA's target installed; the ISA's objdump.
Env:   OBJDUMP_RISCV (default riscv64-unknown-elf-objdump), OBJDUMP_X86 (default objdump),
       OBJDUMP_ARM (default llvm-objdump).
"""

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CRATE = os.path.join(ROOT, "impl", "rust")
RUST_TOOLCHAIN = "1.94.0"
SYMBOL = "avg"


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, text=True, capture_output=True, **kw).stdout


def build_rlib(target, rustflags=""):
    """Build the crate's rlib (an `ar` archive of the object files) and return its path."""
    target_dir = os.path.join(CRATE, "target", "asm-check")  # isolated from normal builds
    env = dict(os.environ, RUSTFLAGS=rustflags, RUSTUP_TOOLCHAIN=RUST_TOOLCHAIN)
    subprocess.run(
        ["cargo", "build", "--quiet", "--release", "--lib", "--target", target,
         "--target-dir", target_dir],
        cwd=CRATE, env=env, check=True,
    )
    rlib = os.path.join(target_dir, target, "release", "libavg.rlib")
    if not os.path.exists(rlib):
        sys.exit(f"missing {rlib}")
    return rlib


def objdump_lines(objdump, flags, obj, strict=False):
    """(raw hex bytes, mnemonic, operand string) for each instruction of SYMBOL."""
    out = run([objdump, "-d", *flags, f"--disassemble={SYMBOL}", obj])
    insns = []
    for line in out.splitlines():
        # riscv: "   0:\t00a5f633          \tand\tx12,x11,x10"
        # x86:   "   0:\t48 89 f0             \tmov    %rsi,%rax"
        m = re.match(r"^\s*[0-9a-f]+:\s+((?:[0-9a-f]{2,8} ?)+)\s+(\S+)\s*(.*?)\s*(#.*)?$", line)
        if m:
            insns.append((m.group(1).replace(" ", ""), m.group(2), m.group(3)))
        elif strict and re.match(r"^\s*[0-9a-f]+:", line):
            sys.exit(f"unparsed instruction in objdump output: {line}")
    if not insns:
        sys.exit(f"symbol `{SYMBOL}` not found in {obj}")
    return insns


def lean_list(path, name="avgProgram", ty="List Instr"):
    """The entries of `def <name> : <ty> := [ ... ]`, whitespace-normalised.

    Entries are split at top-level commas only."""
    src = open(path).read()
    m = re.search(rf"def {re.escape(name)} : {re.escape(ty)} :=\s*\[", src)
    if not m:
        sys.exit(f"could not find `def {name} : {ty} := [` in {path}")
    src = re.sub(r"--[^\n]*", "", src[m.end():])
    entries, cur, depth = [], "", 0
    for ch in src:
        if ch in "[(⟨":
            depth += 1
        elif ch in "])⟩":
            if depth == 0:  # the list's closing `]`
                break
            depth -= 1
        if ch == "," and depth == 0:
            entries.append(cur)
            cur = ""
        else:
            cur += ch
    entries.append(cur)
    return [" ".join(e.split()) for e in entries if e.strip()]


# ---------------------------------------------------------------------------------------------
# RISC-V: riscv-zkvm's `Instr` (RV64IM: no compressed or atomic instructions)
# ---------------------------------------------------------------------------------------------

RISCV_FORMATS = {  # objdump mnemonic -> (Lean constructor, operand kinds). r = reg, i = imm.
    "add": ("ADD", "rrr"), "sub": ("SUB", "rrr"), "and": ("AND", "rrr"),
    "or": ("OR", "rrr"), "xor": ("XOR", "rrr"), "sll": ("SLL", "rrr"),
    "srl": ("SRL", "rrr"), "sra": ("SRA", "rrr"), "slt": ("SLT", "rrr"),
    "sltu": ("SLTU", "rrr"), "mul": ("MUL", "rrr"),
    "addi": ("ADDI", "rri"), "andi": ("ANDI", "rri"), "ori": ("ORI", "rri"),
    "xori": ("XORI", "rri"), "slli": ("SLLI", "rri"), "srli": ("SRLI", "rri"),
    "srai": ("SRAI", "rri"),
}


def riscv_to_lean(raw, mnem, ops):
    if len(raw) != 8:
        sys.exit(f"compressed instruction in output (not RV64IM): {mnem} {ops}")
    ops = [o.strip() for o in ops.split(",")] if ops else []

    def reg(o):
        if not re.fullmatch(r"x([0-9]|[12][0-9]|3[01])", o):
            sys.exit(f"bad register {o}")
        return "." + o

    if mnem == "jalr":  # "x0,0(x1)"
        rd, rest = ops
        m = re.fullmatch(r"(-?\d+)\((x\d+)\)", rest)
        if not m:
            sys.exit(f"cannot parse jalr operands {ops}")
        return f".JALR {reg(rd)} {reg(m.group(2))} {int(m.group(1))}"
    if mnem not in RISCV_FORMATS:
        sys.exit(f"instruction `{mnem} {','.join(ops)}` has no mapping to riscv-zkvm's Instr")
    ctor, kinds = RISCV_FORMATS[mnem]
    if len(ops) != len(kinds):
        sys.exit(f"`{mnem}` expects {len(kinds)} operands, got {ops}")
    return f".{ctor} " + " ".join(reg(o) if k == "r" else str(int(o, 0)) for o, k in zip(ops, kinds))


def check_riscv():
    rlib = build_rlib("riscv64imac-unknown-none-elf", "-C target-feature=-c,-zca,-a")
    objdump = os.environ.get("OBJDUMP_RISCV", "riscv64-unknown-elf-objdump")
    compiled = [riscv_to_lean(*i) for i in objdump_lines(objdump, ["-M", "no-aliases,numeric"], rlib)]
    return compiled, lean_list(os.path.join(ROOT, "backends", "riscv", "AvgRiscv", "Impl.lean"))


# ---------------------------------------------------------------------------------------------
# x86-64: Kraken's parsed AT&T assembly (only the 64-bit forms used by avg)
# ---------------------------------------------------------------------------------------------

X86_GPRS = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
            "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"}
X86_BIN = {"mov", "and", "xor", "add"}


def x86_asm(mnem, ops, disassembled=False):
    """Normalise spelling only; never discard widths, operands or instructions."""
    original = f"{mnem} {ops}".strip()
    ops = [o.strip() for o in ops.split(",")] if ops else []
    if mnem in ({"ret", "retq"} if disassembled else {"ret"}) and not ops:
        return "ret"

    # GNU objdump omits q when register names establish the width. Do not strip
    # arbitrary suffixes: a movl/shrl (or a 32-bit register) must fail, not match.
    base = mnem[:-1] if mnem.endswith("q") else mnem
    if mnem != base + "q" and not disassembled:
        sys.exit(f"expected an explicit 64-bit suffix in x86 assembly: `{original}`")

    def reg(o):
        if not o.startswith("%") or o[1:] not in X86_GPRS:
            sys.exit(f"unsupported x86 operand `{o}` in `{original}` (64-bit GPRs only)")
        return o

    if base in X86_BIN and len(ops) == 2:
        return f"{base}q {reg(ops[0])}, {reg(ops[1])}"
    if base == "shr":
        # D1 /5 has an implicit count of one; GNU may print just the destination.
        if disassembled and len(ops) == 1:
            ops.insert(0, "$1")
        if len(ops) == 2 and re.fullmatch(r"\$(?:0x[0-9a-fA-F]+|[0-9]+)", ops[0]):
            count = int(ops[0][1:], 16 if ops[0].startswith("$0x") else 10)
            if 0 <= count <= 255:
                return f"shrq ${count}, {reg(ops[1])}"
    sys.exit(f"unsupported x86 instruction: `{original}`")


def lean_x86_asm(path):
    """Read the literal passed to Kraken's parse; refuse escapes or other expressions."""
    src = open(path).read()
    m = re.search(r'^\s*def avgProgram\s*:\s*Program\s*:=\s*parse\(\s*"([^"\\]*)"\s*\)\s*$',
                  src, re.M)
    if not m:
        sys.exit(f'could not find `def avgProgram : Program := parse("...")` in {path}')
    instructions = []
    for line in m.group(1).splitlines():
        if not line.strip():
            continue
        parts = line.strip().split(None, 1)
        instructions.append(x86_asm(parts[0], parts[1] if len(parts) == 2 else ""))
    if not instructions:
        sys.exit(f"empty x86 avgProgram in {path}")
    return instructions


def check_x86():
    rlib = build_rlib("x86_64-unknown-linux-gnu")
    objdump = os.environ.get("OBJDUMP_X86", "objdump")
    # AT&T preserves Kraken's source/destination order. Keep all bytes on one line,
    # disassemble zero runs, and reject unparsed instruction lines rather than
    # silently losing an opcode.
    compiled = []
    for raw, mnem, ops in objdump_lines(
            objdump, ["-M", "att", "--insn-width=15", "--disassemble-zeroes"], rlib, strict=True):
        if not re.fullmatch(r"(?:[0-9a-f]{2}){1,15}", raw):
            sys.exit(f"invalid x86 instruction bytes: {raw}")
        compiled.append(x86_asm(mnem, ops, disassembled=True))
    impl = os.path.join(ROOT, "backends", "x86", "AvgX86", "Impl.lean")
    return compiled, lean_x86_asm(impl)


def check_arm():
    rlib = build_rlib("aarch64-unknown-linux-gnu")
    objdump = os.environ.get("OBJDUMP_ARM", "llvm-objdump")
    compiled = []
    for raw, mnem, ops in objdump_lines(objdump, [], rlib):
        if len(raw) != 8:
            sys.exit(f"expected a 32-bit AArch64 instruction word: {raw} {mnem} {ops}")
        compiled.append(f"0x{raw}#32")
    return compiled, lean_list(
        os.path.join(ROOT, "backends", "arm", "AvgArm", "Impl.lean"), ty="List (BitVec 32)")


ISAS = {"riscv": check_riscv, "x86": check_x86, "arm": check_arm}


def main():
    wanted = sys.argv[1:] or list(ISAS)
    failed = []
    for isa in wanted:
        if isa not in ISAS:
            sys.exit(f"unknown ISA `{isa}`; choose from {', '.join(ISAS)}")
        compiled, expected = ISAS[isa]()
        print(f"== {isa}")
        for i in range(max(len(compiled), len(expected))):
            c = compiled[i] if i < len(compiled) else "<none>"
            e = expected[i] if i < len(expected) else "<none>"
            print(f"{'  ' if c == e else '!!'} {i:2}  rustc: {c:44}  lean: {e}")
        if compiled != expected:
            failed.append(isa)
            print(f"rustc's `{SYMBOL}` differs from the {isa} avgProgram. Update the Impl file to match "
                  "(the proof must then be redone).", file=sys.stderr)
        else:
            print(f"OK: rustc's `{SYMBOL}` is exactly the {isa} avgProgram ({len(expected)} instructions).")
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
