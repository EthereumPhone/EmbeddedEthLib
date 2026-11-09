module

public import EthLib.Cryptography.Hash.Keccak.Spec
public import EthLib.Cryptography.Hash.Keccak.FastProofI

/-!
# Keccak

The specification is `Keccak/Spec.lean`, FIPS 202 step by step; every proof reasons about it.

`Keccak/Fast.lean` computes the same functions with every lane an unboxed machine word.

A 32-bit target needs that.

`Keccak/FastProof.lean` proves the straight-line permutation equal to `keccakF`.

It installs it with `@[csimp]`.

It also installs recompiled copies of `keccak512`, `Hasher.absorb` and `Hasher.digest`.

`Keccak/FastProofI.lean` proves the bit-interleaved sponge equal to `keccak256`.

That sponge keeps 32-bit halves, so each 64-bit rotation is two 32-bit rotations.

`FastProofI.lean` installs its guarded form `Fast.keccak256IG` with `@[csimp]`.

Every importer of `EthLib.Cryptography.Hash.Keccak` gets these substitutions through its re-export.
-/
