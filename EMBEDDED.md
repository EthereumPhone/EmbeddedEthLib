# EmbeddedEthLib on 32-bit targets

EmbeddedEthLib is an unofficial fork of [EthLib](https://github.com/ethereum/EthLib) (see the notice in [README.md](README.md)).
It makes the code that Lean compiles from EthLib fast enough for a 32-bit microcontroller, the Cortex-M33 of an STM32U585, without changing what any proof is about.
This file says what was changed and why, lists every fast path with its theorems, and gives the measurements with their caveats.
[`embedded/README.md`](embedded/README.md) says how to reproduce them.

## The method

EthLib's definitions are written to be read against their standards, and its proofs reason about them.
The fork leaves every definition and theorem statement of EthLib as it is.
For a slow function `f` it adds a fast function `g`, a theorem `f = g` that the kernel checks, and the attribute `@[csimp]` on that theorem.
The Lean compiler then compiles every call of `f` as a call of `g`, while every proof still reasons about `f`.

A `@[csimp]` theorem only rewrites code that is compiled after the theorem is in scope.
Two consequences shaped the layout:

- Where a specification module compiles its own callers, the fast form has to be installed for those callers too. So the fork moves the specification into a `Spec` module, byte-identical to upstream's file, and turns the old module name into an aggregator that re-exports the specification and the proof. `EthLib.Cryptography.Hash.Sha256`, `EthLib.Cryptography.Hash.Keccak` and `EthLib.Base.Bytes` are such aggregators. Every module that imported them before now compiles the fast forms, without an import change.
- A function compiled inside a module that the proof has to import gets a copy compiled after the proof, installed by a `rfl` csimp. For example `TweakableHash.lean` compiles `th`, and `trunc_eq` is proved in a module that imports `TweakableHash.lean`, so `thFast`, the same body compiled after `trunc_eq`, replaces `th`. The generated C of a consumer module was checked each time to confirm that it calls the fast symbol.
In the generated C of the whole library, no module outside the SHA-256, Keccak and byte modules calls the specification's `Sha256.hash`, `keccak256` or `readBytes`: 20 files call `Zsf.hashZ`, 47 call `Keccak.Fast.keccak256IG` and 6 call `readBytesP`.

## What was slow, and why

These are properties of Lean 4.35's code generation on a 32-bit target, not of EthLib's code.

- **Boxing.** A 32-bit target has 32-bit pointers, so a `UInt64` stored in an array, a closure or a polymorphic structure field is a heap object. A `Vector UInt8 n` is an `Array` of `n` boxed scalars, 4 bytes each, not a byte buffer, and `ByteArray.data` converts a whole byte buffer into one. Keccak's 25 lanes are `UInt64`.
- **`Nat` arithmetic.** A `Nat` below 2^31 is an unboxed scalar, a larger one a heap object. The leanSPHINCS address encoding builds its bytes through `Nat` division into a `List`, one cons cell per byte.
- **Allocation.** `Vector.ofFn` allocates a closure and builds its array element by element. The specification's SHA-256 allocates as it goes: 250 allocations in the SHA-256 benchmark below, against 28 for the zero-allocation form. The specification's `readBytes` converts the whole buffer once per byte read, so a 7,740-byte signature decode was quadratic. The specification's `sign` rebuilds Merkle trees it has already built.
- **64-bit rotations.** A 64-bit rotation is several 32-bit instructions.
- **The debug-build trap.** Generated C compiled without `-DNDEBUG` keeps `lean.h`'s assertions on every object access. The specification's SHA-256 then executes 2.0 to 3.1 times as many instructions. Every number below is with `-DNDEBUG`.

## The fast paths

Every theorem below is in the library modules (not in `Proofs`), uses only the axioms `propext`, `Classical.choice` and `Quot.sound`, and uses no `sorry`, `native_decide`, `bv_decide`, `implemented_by` or `extern`.

### SHA-256

`EthLib/Cryptography/Hash/Sha256/Spec.lean` is upstream's `Sha256.lean`, unchanged.
`EthLib/Cryptography/Hash/Sha256/Zsf.lean` is the zero-allocation form: every working word is an unboxed `UInt32` parameter of one tail-recursive loop, the message is read in place through a borrow, and `hashInto m out` writes the digest into a caller-owned 32-byte buffer. It does not import the specification.

| theorem (`EthLib.Cryptography.Hash.…`) | statement | `@[csimp]` |
|---|---|---|
| `Sha256.Zsf.hashInto_eq` | `Zsf.hashInto m out = Sha256.hash m` | |
| `Sha256.Zsf.hashZ_eq` | `Zsf.hashZ m = Sha256.hash m` | |
| `Sha256.ZsfProof.hash_eq_hashZ` | `@Sha256.hash = @Zsf.hashZ` | yes |
| `Sha256.ZsfProof.hash32_eq_hash32Z` | `@Sha256.hash32 = @ZsfProof.hash32Z` | yes |
| `sha256_eq_hashZ` | `@sha256 = @Zsf.hashZ` | yes |

The proof is in `Sha256/ZsfProof/` (`Ref`, `Rounds`, `Words`, `Pad`, `Tail`, `Digest`, `Step`, `Loop`, `Main`).
Callers that want no allocation at all call `Sha256.Zsf.hashInto` with a buffer they own; when the buffer is exclusive and 32 bytes long it is written in place.

### Keccak

`EthLib/Cryptography/Hash/Keccak/Spec.lean` is upstream's `Keccak.lean`, unchanged.
`Keccak/Fast.lean` is generated by `embedded/gen/keccak/gen.py` and `gen_i.py`: the permutation as straight-line code over 25 unboxed lanes with literal rotations and round constants, and a bit-interleaved sponge that keeps each lane as two `UInt32` halves (the even and the odd bits), so every 64-bit rotation is two 32-bit rotations.

| theorem (`EthLib.Cryptography.Hash.Keccak.Fast.…`) | statement | `@[csimp]` |
|---|---|---|
| `keccakF2_eq` | `keccakF2 = keccakF` | |
| `keccakF_eq_keccakF2` | `keccakF = keccakF2` | yes |
| `keccak256U_eq` | the in-place sponge `keccak256U` equals `keccak256` | no longer installed |
| `keccakPI_toI` | `keccakPI (toI A) = toI (keccakF A)`, the interleaved permutation | |
| `absorbI_toI`, `squeezeI_eq`, `ofI_toI`, `toI_zero` | the interleaved sponge simulates the specification's | |
| `keccak256I_eq` | `keccak256I msg = keccak256 msg` when `(padF msg).size < USize.size` | |
| `keccak256IG_eq` | `keccak256IG = keccak256`, where `keccak256IG` runs `keccak256I`'s body below 2^31 − 1 padded bytes and the specification above | |
| `keccak256_eq_keccak256IG` | `keccak256 = keccak256IG` | yes |
| `keccak512_eq_keccak512R`, `hasherAbsorb_eq_R`, `hasherDigest_eq_R` | `rfl` copies of `keccak512`, `Hasher.absorb` and `Hasher.digest`, compiled over the fast permutation | yes |

The proofs are in `Keccak/FastProof.lean` and `Keccak/FastProofI.lean` with `FastProofI/Bits.lean` and `FastProofI/Round.lean`, generated by `embedded/gen/keccak/gen_proofI.py`.
The bit facts are `getLsbD` characterisations of the interleaving, and the 24 round constants are a kernel `decide` over `Fin 24`.
`Fast.lean` also keeps experimental sponges (`keccak256F*`, `keccak256G*`, `keccakFU`, `keccakFI`) that were only tested differentially. They have no proof, and no csimp refers to them.

### leanSPHINCS signing

| theorem (`EthLib.Cryptography.…`) | statement | `@[csimp]` |
|---|---|---|
| `Merkle.Fast.climb_siblings` | climbing from a leaf over the specification's path reaches the root | |
| `Merkle.Packed.levels_root`, `levels_path` | the packed tree levels give `Merkle.root` and `Merkle.path` | |
| `Sphincs.treeRootAndPathDF_eq`, `forsOpenAndRootDF_eq`, `forsSignAndKeyDF_eq`, `topPathDF_eq` | the compute-once builders give the specification's roots, paths, FORS openings and keys | |
| `Sphincs.sign_eq_signFast` | `@sign = @signFast` | yes |
| `Sphincs.keyGen_eq_keyGenFast` | `keyGen = keyGenFast` | proved, not installed |

`Sphincs/Fast.lean` builds every tree that `sign` opens once and keeps each level in one `ByteArray`, 16 bytes per digest. The FORS leaf under an opening is computed from the opened secret, so its PRF is not repeated.
`keyGenFast` is not installed because it evaluates the same 264,193 hashes as `keyGen` and holds more memory.
`EthLib.Cryptography.Sphincs` and `EthLib.Cryptography.Exports.Sphincs` import the proof, `Sphincs/FastEq.lean`.

### The leanSPHINCS tweakable hash

`Sphincs/TweakableHash/Fast.lean`, namespace `EthLib.Cryptography.Sphincs.Fast`, imported by `Sphincs/Ots.lean`, the first module that compiles calls of these functions:

| theorem | statement | `@[csimp]` |
|---|---|---|
| `toByte4`, `toByte12` | the specification's `toByte` of a machine word, as its bytes | |
| `encodeAdrs_eq` | `encodeAdrs = encodeAdrsFast`, one 32-element literal from shifts | |
| `adrs_eq`, `keyAdrs_eq`, `adrsChain_eq`, `adrsPk_eq`, `adrsNode_eq`, `adrsPrf_eq`, `adrsEnc_eq`, `adrsFors_eq`, `adrsRoots_eq`, `adrsFprf_eq` | the address builders, recompiled after `encodeAdrs_eq` | yes |
| `trunc_eq` | `@trunc = @truncFast`, one `Array.extract` into an array of exactly 16 elements | yes |
| `th_eq`, `prf_eq` | `rfl` copies of `th` and `prf`, compiled after the theorems above | yes |

Every equality is generic over the monad and the hash, so it also holds in the random-oracle monads of the security proofs.
`truncFast` copies rather than shrinking the hash output in place: a shrunk array keeps a capacity of 32 elements, and a signature holds about 480 digests, which cost about 33 KB more arena at the end of signing and 12.5 KB more at the peak of the whole operation.

### Byte reads

`EthLib/Base/Bytes/Spec.lean` is upstream's `Bytes.lean`, unchanged.

| theorem (`EthLib.Base.…`) | statement | `@[csimp]` |
|---|---|---|
| `copySlice_emptyWithCapacity` | `b.copySlice offset (ByteArray.emptyWithCapacity n) 0 n = b.extract offset (offset + n)` | |
| `readBytes_eq_readBytesP` | `@readBytes = @readBytesP`, one slice copy and one conversion of `n` bytes | yes |

## Measurements

Unless a row says otherwise, the numbers are instructions executed on QEMU `mps2-an505`, a Cortex-M33, counted exactly from QEMU's execution trace (`embedded/tools/count_run.sh`) or, for signing and key generation, with QEMU's instruction counter (`-icount shift=0`, one tick per 50 instructions).
The code is the generated C of this repository, compiled with `arm-none-eabi-gcc` 13.2, `-O2 -DNDEBUG`, and linked with the arena runtime of `embedded/runtime`.
"Upstream" is the same benchmark built from upstream EthLib at `0b028a98`.
Each benchmark segment includes a few tens of instructions of harness (`mark`, `report`).

### leanSPHINCS

All known answers pass in every build: the known-answer signature verifies and the tampered one does not, signing gives the known-answer signature byte for byte, and key generation the known-answer public key.

| operation | upstream | this fork | ratio |
|---|---:|---:|---:|
| decode the public key and the 7,740-byte signature | 874,353,574 | 3,460,788 | 253× |
| verify (valid signature) | 24,390,695 | 12,224,085 | 2.0× |
| key generation | 12.809 G | 6.284 G | 2.0× |
| sign, then encode the signature | 45.93 G | 11.50 G | 4.0× |
| Keccak-256 calls in one signature | 954,172 | 485,244 | 2.0× |

The pieces of a verification, same benchmark:

| piece | upstream | this fork |
|---|---:|---:|
| Keccak-256 of 64 bytes (one permutation) | 33,123 | 17,048 |
| one WOTS chain step (64-byte input) | 44,714 | 20,184 |
| one FORS leaf (PRF of 80 bytes, then F of 64 bytes) | 90,111 | 41,524 |
| one hypertree node hash (80 bytes) | 45,145 | 20,992 |
| one WOTS+C public leaf (257 calls) | 12,436,769 | 6,093,639 |
| T_v (1,072 bytes, 8 permutations) | 304,643 | 215,005 |
| one WOTS+C encoding trial (68 bytes) | 59,675 | 35,222 |

Memory, from the runtime's report (arena peak of live bytes, and stack depth):

| | upstream | this fork |
|---|---:|---:|
| verify mode, arena peak | 123,088 B | 96,680 B |
| sign, arena peak during signing | 71,312 B | 60,792 B |
| sign, arena peak including `encodeSignature` | 104,376 B | 105,400 B |
| key generation, arena peak | 20,544 B | 21,592 B |
| stack, verify / sign / key generation | 13,720 / 15,080 / 14,448 B | 13,812 / 14,940 / 14,540 B |
| closed terms built at initialisation | 1,160 B | 2,240 B |
| instructions before the first mark (initialisation and input loading) | 1,726,440 | 1,842,386 |
| `.text` of the verify benchmark | 105,476 B | 133,276 B |

The whole-operation peak of signing is `encodeSignature`'s, which this fork does not change: it flattens the boxed signature, about 52 KB over the signature itself.
A fast `encodeSignature` writing straight into one 7,740-byte buffer would bring the peak down to about the signing phase's; it is not done.

How the changes add up, each measured on its own in the configuration it was written for:

| change | what was measured | before | after |
|---|---|---:|---:|
| byte reads | decode, upstream otherwise | 874,353,574 | 3,460,788 |
| interleaved Keccak | verify / key generation / sign, upstream otherwise | 24.39 M / 12.81 G / 45.93 G | 16.36 M / 8.51 G / 30.48 G |
| compute-once signing | sign, upstream Keccak | 45.93 G | 23.45 G |
| tweakable hash | verify / key generation / sign, with the in-place Keccak `keccak256U` and an in-place `truncFast` | 17.57 M / 9.153 G / 32.77 G | 13.03 M / 6.701 G / 23.92 G |

Replacing the in-place `truncFast` by the copying one cost about 3.5 % of a verification (11,813,733 to 12,224,085 instructions) and brought the signing peak back from 117,944 B to 105,400 B.

### SHA-256

`embedded/sha256/build.sh` builds one benchmark twice: against `EthLib.Cryptography.Hash.Sha256`, so `Sha256.hash` runs the zero-allocation form, and against `Sha256.Spec` alone, so it runs the specification.
Both give the digests that Python's `hashlib` gives for the same bytes.

| message | specification | zero-allocation form | C reference, `-O2` |
|---|---:|---:|---:|
| 3 bytes | 20,162 | 3,293 | 3,322 |
| 64 bytes | 22,303 | 6,040 | |
| 1,072 bytes | 152,468 | 49,968 | |
| ten 64-byte messages | 228,283 | 65,893 | |
| allocations, whole run | 250 | 28 | |

The C reference is `embedded/sha256/ref.c`, a plain FIPS 180-4 implementation, not tuned: its instructions per hash are the difference of a 1-hash and an 11-hash run, divided by 10.

### Cycles on the STM32U585

These were measured on a B-U585I-IOT02A (STM32U585, Cortex-M33) with code, data, arena and stack in the secure SRAM, read with the DWT cycle counter by `embedded/board/run_on_board.sh`.
SRAM has no wait states and no cache sits in front of it: a load costs 2 cycles and the cycles do not depend on the clock (4 MHz and 160 MHz agreed to within 0.03 %).
Code running from flash, behind the instruction cache and flash wait states, will have other cycle counts.
**None of these runs used the code at the head of this fork.** Each row names what it ran.

SHA-256 of a 3-byte message, cycles per hash:

| code | cycles | ratio to the C reference with the same flags |
|---|---:|---:|
| upstream specification, `-O2`, 4 MHz | 22,477.7 | 5.59 |
| C reference, `-O2`, 4 MHz (4,019.4 with `-O2 -flto` at 160 MHz) | 4,019.7 | 1 |
| zero-allocation form, `-O3 -flto`, 160 MHz | 3,148.6 | 0.83 |
| zero-allocation form, `-O2 -flto`, 160 MHz | 3,194.2 | 0.79 |
| C reference, `-O3 -flto`, 160 MHz | 3,775.6 | 1 |
| C reference, `-O3 -flto -funroll-loops`, 160 MHz | 3,315.5 | |

The specification row ran the specification's code in a standalone harness. The zero-allocation rows ran C that Lean 4.32.2 generated from a standalone copy of the zero-allocation code, not this repository's Lean 4.35.0 build: the two generated C files differ textually, and their equivalence was not shown.
With `-funroll-loops` the C reference is 12 % faster than at `-O3`, so it is a plain reference, not an optimised one.

leanSPHINCS, upstream code (160 MHz), all known answers passing:

| operation | cycles | time at 160 MHz | cycles per instruction |
|---|---:|---:|---:|
| decode the signature | 1,266,303,743 | 7.91 s | 1.448 |
| verify | 34,081,123 | 213 ms | 1.397 |
| key generation | 17,898,791,133 | 111.9 s | 1.397 |
| sign | 64,182,435,221 | 401.1 s | 1.397 |

Projected for this fork (not measured): its QEMU instruction counts times the cycles per instruction measured above give about 31 ms to decode, 107 ms to verify, 55 s for key generation and 100 s to sign, at 160 MHz from SRAM.
The interleaved Keccak has a different mix of instructions, so its cycles per instruction may differ.

### A separate scheme: leanSPHINCS over the HASH accelerator

The STM32U585 has a SHA-256 accelerator.
An experiment replaced Keccak-256 by SHA-256 as leanSPHINCS's hash, once in Lean and once through an `@[extern]` call of the accelerator.
**That is a different signature scheme**: its keys and signatures are not leanSPHINCS's, and no official vectors exist for it.
It needs an `@[extern]` that the kernel cannot check, so it is not part of this fork, and only its measurements are recorded here.
Measured on the board at 160 MHz, with upstream's leanSPHINCS code otherwise:

| operation | upstream (Keccak-256) | SHA-256 in Lean | SHA-256 accelerator |
|---|---:|---:|---:|
| verify | 34.08 M cycles | 18.06 M | 12.08 M |
| key generation | 17.9 G | 9.374 G | 6.209 G |
| sign | 64.2 G | 34.68 G | 23.04 G |

The accelerator hashes a 64-byte message in about 470 cycles, against about 7,900 for the C reference.
With it, about 98 % of a tweakable-hash call is the Lean code around the hash, which the changes of this fork address.

## Caveats

- The arena runtime in `embedded/runtime`, the Lean compiler, the C compiler and the hardware are trusted and unproved, as in upstream's [SOUNDNESS.md](SOUNDNESS.md) section B1.
- A `@[csimp]` theorem equates values, not costs: time, memory and timing side channels are those of the fast form, which is what runs. Nothing here is constant-time.
- The proof-only modules compile to C as well. `Sha256/ZsfProof/Ref.c`, for example, builds reference definitions at initialisation. A firmware that links the SHA-256 aggregator links them; the linker removes what nothing calls, but not their initialisation.
- The unproved experimental Keccak sponges in `Keccak/Fast.lean` are compiled into the library, unused.
- Code that imports only a `Spec` module, or a module compiled before a proof is in scope, runs the specification.
- `embedded/hosttest` calls the library functions, which the C exports wrap. Loading the Exports shared library as a plugin while elaborating the test failed with an undefined symbol, `lp_EthLib_EthLib_Base_ChainConfig_mainnet`; this was observed in this fork's build and not investigated.

## Upstream policy and this fork

EthLib's `lake exe check-decls` reports every `@[csimp]` as a finding, and upstream's `scripts/check_decls_baseline.txt` says never to add one: upstream fixes a finding instead of listing it.
This fork's purpose is those substitutions, so its baseline lists exactly its 23 csimps, each with the module that proves it, and the four `reaches-opaque` findings of the fast forms (they index a `ByteArray` with `USize`, which reaches the opaque `System.Platform.getNumBits`).
Any other finding, and any `extern`, `implemented_by` or extra axiom, still fails the check.
[SOUNDNESS.md](SOUNDNESS.md) section B5 says what the substitutions trust.
The fork also changes `scripts/CheckDecls.lean` to compare baseline entries as text, because a generated private name such as `_private.M.0.f.match_1.splitter` has a numeric component that the old comparison could never match.

## Verification of this fork

At the head of this fork:

- `lake build --wfail EthLib Exports` builds with no warning, with the upstream `lakefile.lean` and its pinned dependencies.
- `lake build Proofs` builds all of EthLib's proofs (6,559 jobs), with Mathlib from `lake exe cache get`. The fork changes no definition, so no proof needed a change.
- `lake exe check-decls` checks 82,680 declarations: 27 findings, all listed in the baseline, none new, none stale. `scripts/test_check_decls.sh` passes.
- `lake env leanchecker` replays every new or changed module (28 modules, at most 10 s each).
- `embedded/hosttest` passes 685 vectors with 1,340 checks: every SHA-256 vector through six paths, every Keccak-256, Keccak-512 and Keccak-f[1600] vector, and every leanSPHINCS key generation, signing and verification vector of `tests/cryptography`.
- `scripts/test_module_system.sh`, `scripts/soundness_facts.py --check`, `scripts/check_layers.py`, `scripts/check_docstrings.py`, `scripts/check_fork_cap.py` and `lake exe gen-bindings --check` pass.

Not yet clean, and not run:

- Upstream's layout gate passes on the whole tree (`scripts/check_lean_layout.py --all --rule wrap`). Its check of the lines a pull request changes (`--base 0b028a98`) still reports 279 findings in the fork's new files: 272 lines longer than 100 characters, most of them generated code and proof steps, and 7 comment lines with no blank line between two sentences.
- The Python bindings' tests (`pytest`), the parity tests and the release checks of upstream's CI were not run.
