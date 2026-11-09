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
`Keccak/Fast.lean` is generated by `embedded/gen/keccak/gen.py` and `gen_i.py` (`embedded/gen/keccak/regen.py` runs them): the permutation as straight-line code over 25 unboxed lanes, two rounds per tail call, with literal rotations and the round constants as the match arms of `rcAt`, and a bit-interleaved sponge that keeps each lane as two `UInt32` halves (the even and the odd bits), so every 64-bit rotation is two 32-bit rotations.

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
`python3 embedded/gen/keccak/regen.py --check` checks that the four generated modules are byte for byte what the generators write.
Every definition in `Fast.lean` is either proved equal to the specification or used by such a proof; the experimental sponges of earlier versions, which had no proof, were removed.

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
Every QEMU run exits with status 0 after it completes and nonzero after a halt or a fault, and `count_run.sh` passes that status on.

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
| `.text` of the verify benchmark | 105,476 B | 133,348 B |

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

The specification's first hash of a run includes a one-time cost.
`compress` reads `K.toList` through a once-cell (`lean_obj_once` in the generated C), so its first call builds a list of 64 cells, which stays live for the rest of the run (64 of the 250 allocations, 1,024 B).
Measured one hash at a time (`embedded/sha256/build.sh first-spec`), the first 3-byte hash takes 20,162 instructions and each later one 13,810 to 13,814.
The zero-allocation form (`build.sh first-fast`) takes 3,293 for every hash.
So the specification's 3-byte row above, and its ratio on the board below, include about 6,350 instructions that a later hash does not pay.

`Sha256.Zsf.hashInto` with one reused, exclusive 32-byte buffer (`embedded/sha256/ShaInto.lean`, `build.sh into`) allocates nothing per hash.
Its cost per hash, as the difference of an 11-hash and a 1-hash segment divided by 10:

| message | instructions per hash |
|---|---:|
| 3 bytes | 3,029.9 (0.91× the C reference) |
| 64 bytes | 5,849.4 |
| 1,072 bytes | 49,106.4 |

The 11-hash segment is also the message's last use, so it frees the message too, which adds about 6, 10 and 73 instructions per hash.

### Cycles on the STM32U585

These were measured on a B-U585I-IOT02A (STM32U585, Cortex-M33) with code, data, arena and stack in the secure SRAM, read with the DWT cycle counter by `embedded/board/run_on_board.sh`.
SRAM has no wait states and no cache sits in front of it: a load costs 2 cycles and the cycles do not depend on the clock (4 MHz and 160 MHz agreed to within 0.03 %).
Code running from flash, behind the instruction cache and flash wait states, will have other cycle counts.

#### This fork's code

The first three tables ran this fork's code at commit `4d4fce1a`, at 160 MHz.
The images were built from this repository as [`embedded/README.md`](embedded/README.md) shows: `embedded/silicon/build.sh` with `-DPQ_MODE=0`, `1` or `2`, `-DARENA_BYTES=393216` and `-DCLK160` for leanSPHINCS, and `embedded/sha256/build.sh fast` or `spec` with `BUILDER=embedded/silicon/build.sh` and `-DCLK160` for SHA-256.
The compiler flags are `-O2 -DNDEBUG`, as for QEMU.
The generated C of the benchmark calls `signFast` for `sign`, `Keccak.Fast.keccak256IG` for `keccak256` and `Zsf.hashZ` for `Sha256.hash`, and the linked `decodeSignature` calls `readBytesP`.
So the fast paths ran through the `@[csimp]` theorems.
`keyGen` has no installed `@[csimp]`: key generation runs the specification's `keyGen` over the fast tweakable hash and the fast Keccak.

All known answers passed on the board.
The known-answer signature verifies, and the same signature with its last bit flipped does not.
Signing gives the known-answer signature byte for byte, and key generation gives the known-answer public key.
Two runs of the verify image agreed to within 16 cycles in each segment.

leanSPHINCS at 160 MHz, cycles (and time):

| operation | upstream code | this fork | ratio | projected for this fork | cycles per instruction, this fork |
|---|---:|---:|---:|---:|---:|
| decode the public key and the 7,740-byte signature | 1,266,303,743 (7.91 s) | 5,049,667 (31.6 ms) | 251× | 31.3 ms | 1.459 |
| verify, valid signature (true) | 34,081,123 (213.0 ms) | 16,481,410 (103.0 ms) | 2.07× | 106.7 ms | 1.348 |
| verify, tampered signature (false) | 34,220,964 (213.9 ms) | 16,621,365 (103.9 ms) | 2.06× | | 1.348 |
| key generation | 17,898,791,133 (111.9 s) | 8,463,163,909 (52.9 s) | 2.11× | 54.9 s | 1.347 |
| sign, then encode the signature | 64,182,435,221 (401.1 s) | 15,493,165,508 (96.8 s) | 4.14× | 100.4 s | 1.347 |

The decode segment includes the copy of the inputs from the known-answer blob, in both columns.
In the sign row, signing alone takes 15,491,490,942 cycles and `encodeSignature` takes 1,674,566 cycles (10.5 ms).
The upstream columns come from the board run of upstream's code that the older table below summarises.
The projection is this fork's QEMU instruction count times the cycles per instruction of upstream's code, and it was made before the board run.
The board measured decode 0.8 % above the projection and the other operations 3.5 % to 3.6 % below it.
The fork's code runs at about 1.35 cycles per instruction, and upstream's at 1.397.
The cycles per instruction of decode and verify use the instruction counts of the QEMU twin of the same image (`embedded/silicon/link_qemu_twin.ld`, traced with `embedded/tools/count_run.sh`).
Those of key generation and signing use the QEMU instruction-counter figures of the leanSPHINCS table above (6.284 G and 11.50 G).

The pieces of a verification, same verify image (cycles):

| piece | upstream code | this fork |
|---|---:|---:|
| Keccak-256 of 64 bytes (one permutation) | 46,151 | 22,747 |
| one WOTS chain step (64-byte input) | 62,591 | 27,134 |
| one FORS leaf (PRF of 80 bytes, then F of 64 bytes) | 125,921 | 55,691 |
| one hypertree node hash (80 bytes) | 63,221 | 28,305 |
| one WOTS+C public leaf (257 calls) | 17,376,955 | 8,205,901 |
| T_v (1,072 bytes, 8 permutations) | 425,165 | 293,200 |
| one WOTS+C encoding trial (68 bytes) | 83,934 | 48,587 |

The arena peaks on the board equal the QEMU figures above: 96,680 B in verify mode, 105,400 B for signing and 21,592 B for key generation.
Every freed byte read zero after the run (`nonzero_in_freed=0`).
The linker wrap of `Keccak.Fast.keccak256IG` counted 1,246 calls in verify mode, 264,193 in key generation and 485,244 in signing.
The cycle counts of key generation and signing exceed 2^32, so `bench_io_silicon.c` extends the 32-bit counter in software.
Two checks show that no wrap was missed: the 64-bit totals agree with the 32-bit cycle word of `bench.h` modulo 2^32, and with the host's wall clock (62 s for key generation and 106 s for signing, each with about 9.5 s of loading and read-back).

SHA-256 at 160 MHz, cycles, the same harness for both columns:

| message | specification | zero-allocation form | ratio |
|---|---:|---:|---:|
| 3 bytes | 32,575 | 4,110 | 7.9× |
| 64 bytes | 37,281 | 7,406 | 5.0× |
| 1,072 bytes | 262,556 | 60,150 | 4.4× |
| ten 64-byte messages | 379,953 | 81,470 | 4.7× |

`fast` runs `Sha256.hash`, which the `@[csimp]` compiles to `Zsf.hashZ`.
`Zsf.hashZ` is `Zsf.hashInto` into a copy of a shared 32-byte zero buffer, so it makes one allocation for each hash.
Each segment holds one hash (ten in the last row) and one `pq_mark`.
Both builds gave the same digests, and two runs of each image agreed to within 1 cycle in each segment.
With the QEMU counts of the SHA-256 table above, the cycles per instruction are about 1.62 to 1.72 for the specification and 1.20 to 1.25 for the zero-allocation form.
On the same day, with the same runner, the C reference `embedded/board/sha/ref_board.c` at `-O2` took 4,019.8 cycles for each 3-byte hash (the difference of a 1-hash and an 11-hash run, divided by 10).
That agrees with the older table below.
The single 3-byte hash of the zero-allocation form, with its `pq_mark` and its allocation, takes 1.02 times as long.
The older table below gives 22,477.7 cycles for the specification.
That figure came from a different, standalone harness and is the average of ten later hashes.
The first hash of this harness also builds the specification's `K.toList` once (6,348 instructions on QEMU, see the SHA-256 section), which accounts for most of the difference: 32,575 − 22,477.7 ≈ 10,100 cycles, about 1.6 cycles per instruction.

`Sha256.Zsf.hashInto` with one reused, exclusive buffer (`embedded/sha256/ShaInto.lean`), cycles per hash at 160 MHz, measured the same way as the C reference:

| message | cycles per hash | ratio to the C reference |
|---|---:|---:|
| 3 bytes | 3,688.1 | 0.92× |
| 64 bytes | 7,078.4 | |
| 1,072 bytes | 59,010.1 | |

These are about 1.20 to 1.22 cycles per instruction of the QEMU counts in the SHA-256 section.

#### Older runs

These runs did not use the code at the head of this fork. Each row names what it ran.

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

This fork's QEMU instruction counts times these cycles per instruction gave the projection column of the first table in "This fork's code".
The projection was made before this fork ran on the board.

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
- Code that imports only a `Spec` module, or a module compiled before a proof is in scope, runs the specification.
- Loading `libEthLib_Exports.so` on its own into Lean (`--load-dynlib` or `--plugin`) fails with an undefined symbol, `lp_EthLib_EthLib_Base_ChainConfig_mainnet`. This is upstream's build, not the fork's: Lake gives each library its own shared library with no `DT_NEEDED` entry for the libraries it imports, so the 820 `lp_EthLib_*` symbols that the exports take from `libEthLib_EthLib.so` resolve only once that library is loaded first, which is what Lake does. Loading `libEthLib_EthLib.so` first works. No upstream flow, `embedded/hosttest` or the Python extension loads the Exports library on its own, and the fork changes none of the files involved.

## Upstream policy and this fork

EthLib's `lake exe check-decls` reports every `@[csimp]` as a finding, and upstream's `scripts/check_decls_baseline.txt` says never to add one: upstream fixes a finding instead of listing it.
This fork's purpose is those substitutions, so its baseline lists exactly its 23 csimps, each with the module that proves it, and the four `reaches-opaque` findings of the fast forms (they index a `ByteArray` with `USize`, which reaches the opaque `System.Platform.getNumBits`).
Any other finding, and any `extern`, `implemented_by` or extra axiom, still fails the check.
[SOUNDNESS.md](SOUNDNESS.md) section B5 says what the substitutions trust.
The fork also changes `scripts/CheckDecls.lean` to compare baseline entries as text, because a generated private name such as `_private.M.0.f.match_1.splitter` has a numeric component that the old comparison could never match.

## Verification of this fork

At the head of this fork:

- `lake build --wfail EthLib Exports` (1,558 jobs) and `lake build --wfail` (6,802 jobs, all of EthLib's proofs included) build with no warning, with the upstream `lakefile.lean` and its pinned dependencies. The fork changes no definition, so no proof needed a change.
- `lake exe check-decls` checks 82,639 declarations: 27 findings, all listed in the baseline, none new, none stale. `scripts/test_check_decls.sh` passes.
- `lake env leanchecker` replays every new or changed module (28 modules, at most 10 s each), and rejects upstream's `scripts/ReplayFixture.lean`, a theorem the kernel never checked. Every installed `@[csimp]` theorem, `keyGen_eq_keyGenFast` and `keccak256U_eq` use only `propext`, `Classical.choice` and `Quot.sound`.
- `embedded/hosttest` passes 685 vectors with 1,340 checks: every SHA-256 vector through six paths, every Keccak-256, Keccak-512 and Keccak-f[1600] vector, and every leanSPHINCS key generation, signing and verification vector of `tests/cryptography`.
- Upstream's Python suites pass against the fork, whose C exports call the fast forms (`Exports/Sha256` calls `Zsf.hashZ`, `Exports/Keccak` calls `keccak256IG` and `keccakF2`, `Exports/Sphincs` calls `signFast`): `uv sync --frozen --extra test`, then `pytest -n auto --dist worksteal` passes 59,618 tests and skips 601 (515 of them need the release archives), with `tests/cryptography` unchanged. Python 3.12 and 3.11 gave the same counts.
- The `slow` suite of `vectors-slow.yml` (`ETHLIB_SLOW_VECTORS=1 pytest -n auto -m "not archive"`, run with `--dist worksteal`) passes 59,683 tests and regenerates every vector unchanged, the leanSPHINCS key generation and signing vectors among them. The consensus parity catalogue of `ci.yml`, with its two archives fetched, passes.
- The `vectors`, `python` (`ruff check`, `ruff format --check`, `ty check`, codespell) and `soundness` jobs of `ci.yml` pass, as do `scripts/test_module_system.sh`, the timing and build-pipeline unit tests, `lake exe gen-bindings --check` and `uv build --sdist`.
- Upstream's layout gate reports no finding on the whole tree (`scripts/check_lean_layout.py --all --rule wrap`, which CI runs on every push), and `scripts/check_python_comments.py --all` none either. Against upstream (`--base 0b028a98`) the only findings are five in `Hash/Keccak/Spec.lean`: that file is upstream's `Keccak.lean` byte for byte, which the check counts as new because the module moved. A pull request into this fork is checked against the fork's own base, where the file is not new.
- `python3 embedded/gen/keccak/regen.py --check` passes: the generators write the committed Keccak modules byte for byte.
- On QEMU, the verify benchmark exits with status 0, prints the expected known answers, and its traced counts equal the tables above.
- On a B-U585I-IOT02A, from SRAM at 160 MHz, the leanSPHINCS and SHA-256 board images built from this repository pass every known answer (see "This fork's code" under "Cycles on the STM32U585").

This fork's workflows run CI on `main`, and `publish.yml` runs only in `ethereum/EthLib`, so the fork never publishes to PyPI.
The weekly schedules of `replay.yml` and `vectors-slow.yml` are kept.

Not run:

- The suites on Python 3.10, 3.13, 3.14 and 3.14t.
- The archive suites of `vectors-slow.yml` (the execution, consensus, devnet and legacy parity runs, which upstream measures in hours, and the execution-spec-tests, consensus SSZ, ssz-generic and NIST CAVP archives), `tests/cryptography/check_vectors.py --upstream`, and `scripts/check_spec_releases.py`, which queries the GitHub API.
- `scripts/replay.sh` over all of EthLib's modules: only the fork's 28 new or changed modules were replayed.
- The memory check of a pull request's changed files, and the wheel builds of `publish.yml`.
