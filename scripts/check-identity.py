#!/usr/bin/env python3
"""Exercise the independent identity example's one-argument C ABI on x86-64 Linux."""

import argparse
import ctypes
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    directory = parser.parse_args().directory.resolve()
    compiler = os.environ.get("CC", "cc")
    with tempfile.TemporaryDirectory(prefix="identity-ffi-") as temporary:
        output = Path(temporary)
        shared = output / "identity.so"
        subprocess.run([compiler, "-shared", "-fPIC", str(directory / "identity_u64.s"),
                        "-o", str(shared)], check=True)
        library = ctypes.CDLL(str(shared))
        library.identity_u64.argtypes = [ctypes.c_uint64]
        library.identity_u64.restype = ctypes.c_uint64
        for value in [0, 1, 42, (1 << 63) - 1, 1 << 63, (1 << 64) - 1]:
            if library.identity_u64(value) != value:
                raise SystemExit(f"identity_u64({value}) returned the wrong value")
        source = output / "main.c"
        source.write_text('''#include "identity_u64.h"
#include <assert.h>
int main(void) {
    assert(identity_u64(42) == 42);
    assert(identity_u64(UINT64_MAX) == UINT64_MAX);
    return 0;
}
''')
        executable = output / "check"
        subprocess.run([compiler, "-Wall", "-Wextra", "-Werror", "-I", str(directory),
                        str(source), str(directory / "identity_u64.s"), "-o", str(executable)], check=True)
        subprocess.run([str(executable)], check=True)
    print("PASS: independent one-argument identity function through Python FFI and C")


if __name__ == "__main__":
    main()
