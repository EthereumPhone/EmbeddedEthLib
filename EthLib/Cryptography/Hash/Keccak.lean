module

public import EthLib.Cryptography.Hash.Keccak.Spec
public import EthLib.Cryptography.Hash.Keccak.FastProofI

/-!
# Keccak

The specification is `Keccak/Spec.lean`, FIPS 202 step by step; every proof reasons about it.

`Keccak/Fast.lean` computes the same functions with every lane an unboxed machine word, which a 32-bit target needs. `Keccak/FastProof.lean` proves the straight-line permutation equal to `keccakF` and installs it with `@[csimp]`, together with recompiled copies of `keccak512`, `Hasher.absorb` and `Hasher.digest`. `Keccak/FastProofI.lean` proves the bit-interleaved sponge (32-bit halves, so each 64-bit rotation is two 32-bit rotations) equal to `keccak256` and installs its guarded form `Fast.keccak256IG` with `@[csimp]`. Every importer of `EthLib.Cryptography.Hash.Keccak` gets these substitutions through the public re-export.
-/
