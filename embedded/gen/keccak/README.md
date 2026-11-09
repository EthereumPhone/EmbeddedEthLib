# Generators of the Keccak fast path

These scripts write four Lean modules under `EthLib/Cryptography/Hash/Keccak/`:

| module | written by |
|---|---|
| `Fast.lean` | `gen.py`, then `gen_i.py`, which appends the bit-interleaved form |
| `FastProofI.lean`, `FastProofI/Bits.lean`, `FastProofI/Round.lean` | `gen_proofI.py` |

`gen_proofI.py` takes the first round of `loopI2` from the function of `gen_i.py` that emits it, so the proof and the code it proves come from one source.

Do not edit the four modules by hand.
Change the generators, then regenerate.
From the root of the repository:

```bash
python3 embedded/gen/keccak/regen.py
```

To check that the committed modules are exactly what the generators write:

```bash
python3 embedded/gen/keccak/regen.py --check
```

The check regenerates the modules into a temporary directory and compares each one byte for byte.
It exits with status 1 and names every module that differs.
`FastProof.lean` is not generated.
`layout.py` breaks the long runs of names and arguments into lines of at most 100 characters, the limit of `scripts/check_lean_layout.py`.
