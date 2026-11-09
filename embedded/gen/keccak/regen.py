#!/usr/bin/env python3
"""Regenerate the four generated Keccak modules, or check that they match their generators."""

# From the root of the repository:
#
#     python3 embedded/gen/keccak/regen.py           # write the four modules in place
#     python3 embedded/gen/keccak/regen.py --check   # regenerate into a temporary directory and compare
#
# gen.py, then gen_i.py, write `EthLib/Cryptography/Hash/Keccak/Fast.lean`.
#
# gen_proofI.py writes `FastProofI.lean`, `FastProofI/Bits.lean` and `FastProofI/Round.lean`.
#
# `--check` exits with status 1 and names each module that differs from its generated text.

import filecmp
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
TARGET = os.path.join(HERE, "..", "..", "..", "EthLib", "Cryptography", "Hash", "Keccak")
MODULES = ["Fast.lean", "FastProofI.lean", "FastProofI/Bits.lean", "FastProofI/Round.lean"]


def generate(directory):
    """Write the four generated modules into `directory`."""
    os.makedirs(os.path.join(directory, "FastProofI"), exist_ok=True)
    fast = os.path.join(directory, "Fast.lean")
    for script, arg in (("gen.py", fast), ("gen_i.py", fast), ("gen_proofI.py", directory)):
        subprocess.run([sys.executable, "-B", os.path.join(HERE, script), arg], check=True)


def main(argv):
    if argv[1:] == ["--check"]:
        with tempfile.TemporaryDirectory() as tmp:
            generate(tmp)
            differ = [
                m
                for m in MODULES
                if not filecmp.cmp(os.path.join(tmp, m), os.path.join(TARGET, m), shallow=False)
            ]
        for m in differ:
            print(f"differs from its generated text: EthLib/Cryptography/Hash/Keccak/{m}")
        if not differ:
            print("All four generated Keccak modules match their generators byte for byte.")
        return 1 if differ else 0
    if argv[1:]:
        print("usage: regen.py [--check]")
        return 2
    generate(TARGET)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
