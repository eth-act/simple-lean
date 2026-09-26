#!/usr/bin/env python3
"""Example-specific smoke test for avg; all compiled binaries are temporary.

Usage: python3 scripts/check-avg.py dist/x86
Requires a native C compiler (CC, default cc). No Rust or Lean runtime is used.
"""

import argparse
import ctypes
import os
from pathlib import Path
import platform
import random
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    directory = args.directory.resolve()
    with tempfile.TemporaryDirectory(prefix="avg-ffi-") as temporary:
        compiler = os.environ.get("CC", "cc")
        shared = Path(temporary) / "libavg.so"
        subprocess.run([compiler, "-shared", "-fPIC", str(directory / "avg.s"),
                        "-o", str(shared)], check=True)
        library = ctypes.CDLL(str(shared))
        library.avg.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
        library.avg.restype = ctypes.c_uint64
        maximum = (1 << 64) - 1
        edges = [0, 1, 2, 3, (1 << 63) - 1, 1 << 63, maximum - 1, maximum]
        pairs = [(a, b) for a in edges for b in edges]
        rng = random.Random(0)
        pairs.extend((rng.getrandbits(64), rng.getrandbits(64)) for _ in range(1000))
        for a, b in pairs:
            actual = library.avg(a, b)
            expected = (a + b) // 2
            if actual != expected:
                raise SystemExit(f"avg({a}, {b}) returned {actual}, expected {expected}")
        source = Path(temporary) / "main.c"
        source.write_text('''#include "avg.h"
#include <assert.h>
int main(void) {
    assert(avg(3, 4) == 3);
    assert(avg(UINT64_MAX, UINT64_MAX) == UINT64_MAX);
    assert(avg(0, UINT64_MAX) == UINT64_MAX / 2);
    assert(avg(UINT64_MAX, UINT64_MAX - 1) == UINT64_MAX - 1);
    return 0;
}
''')
        executable = Path(temporary) / "check"
        subprocess.run([compiler, "-Wall", "-Wextra", "-Werror",
                        "-I", str(directory), str(source), str(directory / "avg.s"),
                        "-o", str(executable)], check=True)
        subprocess.run([str(executable)], check=True)
    print(f"PASS ({platform.machine()}): {len(pairs)} Python FFI calls and C assembly caller")


if __name__ == "__main__":
    main()
