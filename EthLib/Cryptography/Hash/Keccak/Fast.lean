module

public import EthLib.Cryptography.Hash.Keccak.Spec

/-!
# Keccak, fast form

The functions here compute `keccakF` and `keccak256` of `EthLib.Cryptography.Hash.Keccak`.

They are written so that a 32-bit target keeps all 25 lanes of the state unboxed.

The lanes are `UInt64` parameters and locals, and each round is straight-line code.

Every rotation is by a literal amount, and `rcAt` gives the round constants as match arms.

The bit-interleaved form keeps each lane as two `UInt32` halves, its even and its odd bits.

`embedded/gen/keccak/gen.py` and `gen_i.py` generate this file, and `regen.py` runs them.

`Keccak/FastProof.lean` proves `keccakF1 = keccakF` and `keccakF2 = keccakF`.

It installs `keccakF2` with `@[csimp]`, and proves `padF msg = pad RATE msg`.

It also proves the in-place sponge `keccak256U` equal to `keccak256`, and does not install it.

`Keccak/FastProofI.lean` proves that the bit-interleaved sponge `keccak256I` equals `keccak256`.

That holds whenever `(padF msg).size < USize.size`.

`FastProofI.lean` installs `keccak256IG` for `keccak256` with `@[csimp]`.

`keccak256IG` runs the body of `keccak256I` when the padded message is shorter than `2^31 - 1`.

Otherwise it runs the specification.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak.Fast
open EthLib.Cryptography.Hash.Keccak

/-- `RC[i]` as match arms, so it compiles to a switch rather than a boxed-array lookup. -/
def rcAt : UInt32 → UInt64
  | 0 => 0x0000000000000001
  | 1 => 0x0000000000008082
  | 2 => 0x800000000000808A
  | 3 => 0x8000000080008000
  | 4 => 0x000000000000808B
  | 5 => 0x0000000080000001
  | 6 => 0x8000000080008081
  | 7 => 0x8000000000008009
  | 8 => 0x000000000000008A
  | 9 => 0x0000000000000088
  | 10 => 0x0000000080008009
  | 11 => 0x000000008000000A
  | 12 => 0x000000008000808B
  | 13 => 0x800000000000008B
  | 14 => 0x8000000000008089
  | 15 => 0x8000000000008003
  | 16 => 0x8000000000008002
  | 17 => 0x8000000000000080
  | 18 => 0x000000000000800A
  | 19 => 0x800000008000000A
  | 20 => 0x8000000080008081
  | 21 => 0x8000000000008080
  | 22 => 0x0000000080000001
  | 23 => 0x8000000080008008
  | _ => 0

/-- `n` more rounds from round `i`, one round per tail call. -/
def loop1 : Nat → UInt32 → (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64) → State
  | 0, _, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24 => ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24⟩
  | n + 1, i, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24 =>
    let c0 := a0 ^^^ a5 ^^^ a10 ^^^ a15 ^^^ a20
    let c1 := a1 ^^^ a6 ^^^ a11 ^^^ a16 ^^^ a21
    let c2 := a2 ^^^ a7 ^^^ a12 ^^^ a17 ^^^ a22
    let c3 := a3 ^^^ a8 ^^^ a13 ^^^ a18 ^^^ a23
    let c4 := a4 ^^^ a9 ^^^ a14 ^^^ a19 ^^^ a24
    let d0 := c4 ^^^ rotl c1 1
    let d1 := c0 ^^^ rotl c2 1
    let d2 := c1 ^^^ rotl c3 1
    let d3 := c2 ^^^ rotl c4 1
    let d4 := c3 ^^^ rotl c0 1
    let r0 := rotl (a0 ^^^ d0) 0
    let r1 := rotl (a1 ^^^ d1) 1
    let r2 := rotl (a2 ^^^ d2) 62
    let r3 := rotl (a3 ^^^ d3) 28
    let r4 := rotl (a4 ^^^ d4) 27
    let r5 := rotl (a5 ^^^ d0) 36
    let r6 := rotl (a6 ^^^ d1) 44
    let r7 := rotl (a7 ^^^ d2) 6
    let r8 := rotl (a8 ^^^ d3) 55
    let r9 := rotl (a9 ^^^ d4) 20
    let r10 := rotl (a10 ^^^ d0) 3
    let r11 := rotl (a11 ^^^ d1) 10
    let r12 := rotl (a12 ^^^ d2) 43
    let r13 := rotl (a13 ^^^ d3) 25
    let r14 := rotl (a14 ^^^ d4) 39
    let r15 := rotl (a15 ^^^ d0) 41
    let r16 := rotl (a16 ^^^ d1) 45
    let r17 := rotl (a17 ^^^ d2) 15
    let r18 := rotl (a18 ^^^ d3) 21
    let r19 := rotl (a19 ^^^ d4) 8
    let r20 := rotl (a20 ^^^ d0) 18
    let r21 := rotl (a21 ^^^ d1) 2
    let r22 := rotl (a22 ^^^ d2) 61
    let r23 := rotl (a23 ^^^ d3) 56
    let r24 := rotl (a24 ^^^ d4) 14
    let e0 := (r0 ^^^ (~~~r6 &&& r12)) ^^^ rcAt i
    let e1 := r6 ^^^ (~~~r12 &&& r18)
    let e2 := r12 ^^^ (~~~r18 &&& r24)
    let e3 := r18 ^^^ (~~~r24 &&& r0)
    let e4 := r24 ^^^ (~~~r0 &&& r6)
    let e5 := r3 ^^^ (~~~r9 &&& r10)
    let e6 := r9 ^^^ (~~~r10 &&& r16)
    let e7 := r10 ^^^ (~~~r16 &&& r22)
    let e8 := r16 ^^^ (~~~r22 &&& r3)
    let e9 := r22 ^^^ (~~~r3 &&& r9)
    let e10 := r1 ^^^ (~~~r7 &&& r13)
    let e11 := r7 ^^^ (~~~r13 &&& r19)
    let e12 := r13 ^^^ (~~~r19 &&& r20)
    let e13 := r19 ^^^ (~~~r20 &&& r1)
    let e14 := r20 ^^^ (~~~r1 &&& r7)
    let e15 := r4 ^^^ (~~~r5 &&& r11)
    let e16 := r5 ^^^ (~~~r11 &&& r17)
    let e17 := r11 ^^^ (~~~r17 &&& r23)
    let e18 := r17 ^^^ (~~~r23 &&& r4)
    let e19 := r23 ^^^ (~~~r4 &&& r5)
    let e20 := r2 ^^^ (~~~r8 &&& r14)
    let e21 := r8 ^^^ (~~~r14 &&& r15)
    let e22 := r14 ^^^ (~~~r15 &&& r21)
    let e23 := r15 ^^^ (~~~r21 &&& r2)
    let e24 := r21 ^^^ (~~~r2 &&& r8)
    loop1 n (i + 1) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24

/-- `2n` more rounds from round `i`, two rounds per tail call. -/
def loop2 : Nat → UInt32 → (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64) → State
  | 0, _, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24 => ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24⟩
  | n + 1, i, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24 =>
    let c0_0 := a0 ^^^ a5 ^^^ a10 ^^^ a15 ^^^ a20
    let c1_0 := a1 ^^^ a6 ^^^ a11 ^^^ a16 ^^^ a21
    let c2_0 := a2 ^^^ a7 ^^^ a12 ^^^ a17 ^^^ a22
    let c3_0 := a3 ^^^ a8 ^^^ a13 ^^^ a18 ^^^ a23
    let c4_0 := a4 ^^^ a9 ^^^ a14 ^^^ a19 ^^^ a24
    let d0_0 := c4_0 ^^^ rotl c1_0 1
    let d1_0 := c0_0 ^^^ rotl c2_0 1
    let d2_0 := c1_0 ^^^ rotl c3_0 1
    let d3_0 := c2_0 ^^^ rotl c4_0 1
    let d4_0 := c3_0 ^^^ rotl c0_0 1
    let r0_0 := rotl (a0 ^^^ d0_0) 0
    let r1_0 := rotl (a1 ^^^ d1_0) 1
    let r2_0 := rotl (a2 ^^^ d2_0) 62
    let r3_0 := rotl (a3 ^^^ d3_0) 28
    let r4_0 := rotl (a4 ^^^ d4_0) 27
    let r5_0 := rotl (a5 ^^^ d0_0) 36
    let r6_0 := rotl (a6 ^^^ d1_0) 44
    let r7_0 := rotl (a7 ^^^ d2_0) 6
    let r8_0 := rotl (a8 ^^^ d3_0) 55
    let r9_0 := rotl (a9 ^^^ d4_0) 20
    let r10_0 := rotl (a10 ^^^ d0_0) 3
    let r11_0 := rotl (a11 ^^^ d1_0) 10
    let r12_0 := rotl (a12 ^^^ d2_0) 43
    let r13_0 := rotl (a13 ^^^ d3_0) 25
    let r14_0 := rotl (a14 ^^^ d4_0) 39
    let r15_0 := rotl (a15 ^^^ d0_0) 41
    let r16_0 := rotl (a16 ^^^ d1_0) 45
    let r17_0 := rotl (a17 ^^^ d2_0) 15
    let r18_0 := rotl (a18 ^^^ d3_0) 21
    let r19_0 := rotl (a19 ^^^ d4_0) 8
    let r20_0 := rotl (a20 ^^^ d0_0) 18
    let r21_0 := rotl (a21 ^^^ d1_0) 2
    let r22_0 := rotl (a22 ^^^ d2_0) 61
    let r23_0 := rotl (a23 ^^^ d3_0) 56
    let r24_0 := rotl (a24 ^^^ d4_0) 14
    let b0 := (r0_0 ^^^ (~~~r6_0 &&& r12_0)) ^^^ rcAt i
    let b1 := r6_0 ^^^ (~~~r12_0 &&& r18_0)
    let b2 := r12_0 ^^^ (~~~r18_0 &&& r24_0)
    let b3 := r18_0 ^^^ (~~~r24_0 &&& r0_0)
    let b4 := r24_0 ^^^ (~~~r0_0 &&& r6_0)
    let b5 := r3_0 ^^^ (~~~r9_0 &&& r10_0)
    let b6 := r9_0 ^^^ (~~~r10_0 &&& r16_0)
    let b7 := r10_0 ^^^ (~~~r16_0 &&& r22_0)
    let b8 := r16_0 ^^^ (~~~r22_0 &&& r3_0)
    let b9 := r22_0 ^^^ (~~~r3_0 &&& r9_0)
    let b10 := r1_0 ^^^ (~~~r7_0 &&& r13_0)
    let b11 := r7_0 ^^^ (~~~r13_0 &&& r19_0)
    let b12 := r13_0 ^^^ (~~~r19_0 &&& r20_0)
    let b13 := r19_0 ^^^ (~~~r20_0 &&& r1_0)
    let b14 := r20_0 ^^^ (~~~r1_0 &&& r7_0)
    let b15 := r4_0 ^^^ (~~~r5_0 &&& r11_0)
    let b16 := r5_0 ^^^ (~~~r11_0 &&& r17_0)
    let b17 := r11_0 ^^^ (~~~r17_0 &&& r23_0)
    let b18 := r17_0 ^^^ (~~~r23_0 &&& r4_0)
    let b19 := r23_0 ^^^ (~~~r4_0 &&& r5_0)
    let b20 := r2_0 ^^^ (~~~r8_0 &&& r14_0)
    let b21 := r8_0 ^^^ (~~~r14_0 &&& r15_0)
    let b22 := r14_0 ^^^ (~~~r15_0 &&& r21_0)
    let b23 := r15_0 ^^^ (~~~r21_0 &&& r2_0)
    let b24 := r21_0 ^^^ (~~~r2_0 &&& r8_0)
    let c0_1 := b0 ^^^ b5 ^^^ b10 ^^^ b15 ^^^ b20
    let c1_1 := b1 ^^^ b6 ^^^ b11 ^^^ b16 ^^^ b21
    let c2_1 := b2 ^^^ b7 ^^^ b12 ^^^ b17 ^^^ b22
    let c3_1 := b3 ^^^ b8 ^^^ b13 ^^^ b18 ^^^ b23
    let c4_1 := b4 ^^^ b9 ^^^ b14 ^^^ b19 ^^^ b24
    let d0_1 := c4_1 ^^^ rotl c1_1 1
    let d1_1 := c0_1 ^^^ rotl c2_1 1
    let d2_1 := c1_1 ^^^ rotl c3_1 1
    let d3_1 := c2_1 ^^^ rotl c4_1 1
    let d4_1 := c3_1 ^^^ rotl c0_1 1
    let r0_1 := rotl (b0 ^^^ d0_1) 0
    let r1_1 := rotl (b1 ^^^ d1_1) 1
    let r2_1 := rotl (b2 ^^^ d2_1) 62
    let r3_1 := rotl (b3 ^^^ d3_1) 28
    let r4_1 := rotl (b4 ^^^ d4_1) 27
    let r5_1 := rotl (b5 ^^^ d0_1) 36
    let r6_1 := rotl (b6 ^^^ d1_1) 44
    let r7_1 := rotl (b7 ^^^ d2_1) 6
    let r8_1 := rotl (b8 ^^^ d3_1) 55
    let r9_1 := rotl (b9 ^^^ d4_1) 20
    let r10_1 := rotl (b10 ^^^ d0_1) 3
    let r11_1 := rotl (b11 ^^^ d1_1) 10
    let r12_1 := rotl (b12 ^^^ d2_1) 43
    let r13_1 := rotl (b13 ^^^ d3_1) 25
    let r14_1 := rotl (b14 ^^^ d4_1) 39
    let r15_1 := rotl (b15 ^^^ d0_1) 41
    let r16_1 := rotl (b16 ^^^ d1_1) 45
    let r17_1 := rotl (b17 ^^^ d2_1) 15
    let r18_1 := rotl (b18 ^^^ d3_1) 21
    let r19_1 := rotl (b19 ^^^ d4_1) 8
    let r20_1 := rotl (b20 ^^^ d0_1) 18
    let r21_1 := rotl (b21 ^^^ d1_1) 2
    let r22_1 := rotl (b22 ^^^ d2_1) 61
    let r23_1 := rotl (b23 ^^^ d3_1) 56
    let r24_1 := rotl (b24 ^^^ d4_1) 14
    let e0 := (r0_1 ^^^ (~~~r6_1 &&& r12_1)) ^^^ rcAt (i + 1)
    let e1 := r6_1 ^^^ (~~~r12_1 &&& r18_1)
    let e2 := r12_1 ^^^ (~~~r18_1 &&& r24_1)
    let e3 := r18_1 ^^^ (~~~r24_1 &&& r0_1)
    let e4 := r24_1 ^^^ (~~~r0_1 &&& r6_1)
    let e5 := r3_1 ^^^ (~~~r9_1 &&& r10_1)
    let e6 := r9_1 ^^^ (~~~r10_1 &&& r16_1)
    let e7 := r10_1 ^^^ (~~~r16_1 &&& r22_1)
    let e8 := r16_1 ^^^ (~~~r22_1 &&& r3_1)
    let e9 := r22_1 ^^^ (~~~r3_1 &&& r9_1)
    let e10 := r1_1 ^^^ (~~~r7_1 &&& r13_1)
    let e11 := r7_1 ^^^ (~~~r13_1 &&& r19_1)
    let e12 := r13_1 ^^^ (~~~r19_1 &&& r20_1)
    let e13 := r19_1 ^^^ (~~~r20_1 &&& r1_1)
    let e14 := r20_1 ^^^ (~~~r1_1 &&& r7_1)
    let e15 := r4_1 ^^^ (~~~r5_1 &&& r11_1)
    let e16 := r5_1 ^^^ (~~~r11_1 &&& r17_1)
    let e17 := r11_1 ^^^ (~~~r17_1 &&& r23_1)
    let e18 := r17_1 ^^^ (~~~r23_1 &&& r4_1)
    let e19 := r23_1 ^^^ (~~~r4_1 &&& r5_1)
    let e20 := r2_1 ^^^ (~~~r8_1 &&& r14_1)
    let e21 := r8_1 ^^^ (~~~r14_1 &&& r15_1)
    let e22 := r14_1 ^^^ (~~~r15_1 &&& r21_1)
    let e23 := r15_1 ^^^ (~~~r21_1 &&& r2_1)
    let e24 := r21_1 ^^^ (~~~r2_1 &&& r8_1)
    loop2 n (i + 2) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24

/-- Keccak-f[1600], one round per tail call. -/
def keccakF1 (A : State) : State :=
  loop1 24 0 A.a0 A.a1 A.a2 A.a3 A.a4 A.a5 A.a6 A.a7 A.a8 A.a9 A.a10 A.a11 A.a12 A.a13 A.a14
    A.a15 A.a16 A.a17 A.a18 A.a19 A.a20 A.a21 A.a22 A.a23 A.a24

/-- Keccak-f[1600], two rounds per tail call. -/
def keccakF2 (A : State) : State :=
  loop2 12 0 A.a0 A.a1 A.a2 A.a3 A.a4 A.a5 A.a6 A.a7 A.a8 A.a9 A.a10 A.a11 A.a12 A.a13 A.a14
    A.a15 A.a16 A.a17 A.a18 A.a19 A.a20 A.a21 A.a22 A.a23 A.a24

/-! ## Padding and the digest of Keccak-256 -/

def zeros136 : ByteArray := ⟨Array.replicate 136 0⟩

/-- `pad RATE msg` built with byte-array copies instead of a boxed `Array UInt8`. -/
def padF (msg : ByteArray) : ByteArray :=
  let k := RATE - msg.size % RATE
  let b := (ByteArray.emptyWithCapacity (msg.size + k)).append msg
  let b := zeros136.copySlice 0 b b.size k
  let b := b.set! msg.size (b.get! msg.size ||| 0x01)
  b.set! (b.size - 1) (b.get! (b.size - 1) ||| 0x80)

/-- The 32 digest bytes of lanes 0 to 3, least significant first, in one array. -/
def squeezeF (S : State) : Vector UInt8 DIGEST_LEN :=
  let a := S.a0; let b := S.a1; let c := S.a2; let d := S.a3
  ⟨#[a.toUInt8, (a >>> 8).toUInt8, (a >>> 16).toUInt8, (a >>> 24).toUInt8,
     (a >>> 32).toUInt8, (a >>> 40).toUInt8, (a >>> 48).toUInt8, (a >>> 56).toUInt8,
     b.toUInt8, (b >>> 8).toUInt8, (b >>> 16).toUInt8, (b >>> 24).toUInt8,
     (b >>> 32).toUInt8, (b >>> 40).toUInt8, (b >>> 48).toUInt8, (b >>> 56).toUInt8,
     c.toUInt8, (c >>> 8).toUInt8, (c >>> 16).toUInt8, (c >>> 24).toUInt8,
     (c >>> 32).toUInt8, (c >>> 40).toUInt8, (c >>> 48).toUInt8, (c >>> 56).toUInt8,
     d.toUInt8, (d >>> 8).toUInt8, (d >>> 16).toUInt8, (d >>> 24).toUInt8,
     (d >>> 32).toUInt8, (d >>> 40).toUInt8, (d >>> 48).toUInt8, (d >>> 56).toUInt8], rfl⟩

/-! ## Lane reads without bounds checks or `Nat` arithmetic -/

theorem idx_lt {p s : Nat} (h : p + 136 ≤ s) (c : Nat) (hc : c < 136) :
    (USize.ofNat p + USize.ofNat c).toNat < s := by
  rw [USize.toNat_add]
  have h1 := Nat.mod_le ((USize.ofNat p).toNat + (USize.ofNat c).toNat) (2 ^ System.Platform.numBits)
  have h2 : (USize.ofNat p).toNat ≤ p := by rw [USize.toNat_ofNat']; exact Nat.mod_le _ _
  have h3 : (USize.ofNat c).toNat ≤ c := by rw [USize.toNat_ofNat']; exact Nat.mod_le _ _
  omega

/-- Byte `c` of the block at `p`, as a `UInt32`, read in place. -/
@[inline] def rdb (bytes : @& ByteArray) (p : Nat) (h : p + 136 ≤ bytes.size) (q : USize)
    (hq : q = USize.ofNat p) (c : Nat) (hc : c < 136) : UInt32 :=
  (bytes.uget (q + USize.ofNat c) (hq ▸ idx_lt h c hc)).toUInt32

/-- The little-endian word of bytes `c` to `c + 3` of the block at `p`. -/
@[inline] def lane32 (bytes : @& ByteArray) (p : Nat) (h : p + 136 ≤ bytes.size) (q : USize)
    (hq : q = USize.ofNat p) (c : Nat) (hc : c + 4 ≤ 136) : UInt32 :=
  rdb bytes p h q hq c (by omega) ||| rdb bytes p h q hq (c + 1) (by omega) <<< 8 |||
    rdb bytes p h q hq (c + 2) (by omega) <<< 16 ||| rdb bytes p h q hq (c + 3) (by omega) <<< 24

/-! ## Bit-interleaved form: each lane as two `UInt32`, its even and its odd bits

A 64-bit rotation by `2m` rotates both halves by `m`; by `2m + 1` it swaps them and rotates by `m + 1` and `m`. So every operation of a round is a 32-bit operation, which Thumb-2 does in one instruction, with the rotations folded into the operands of `eor`/`bic`. -/

/-- The state in bit-interleaved form: field `kE` holds the even bits of lane `k`, `kO` the odd bits. -/
structure StateI where
  (e0 o0 e1 o1 e2 o2 e3 o3 e4 o4 e5 o5 e6 o6 e7 o7 e8 o8 e9 o9 e10 o10 e11 o11 e12 o12 e13 o13 e14 o14 e15 o15 e16 o16 e17 o17 e18 o18 e19 o19 e20 o20 e21 o21 e22 o22 e23 o23 e24 o24 : UInt32)

@[inline] def rol32 (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

def rcE : UInt32 → UInt32
  | 0 => 0x00000001
  | 1 => 0x00000000
  | 2 => 0x00000000
  | 3 => 0x00000000
  | 4 => 0x00000001
  | 5 => 0x00000001
  | 6 => 0x00000001
  | 7 => 0x00000001
  | 8 => 0x00000000
  | 9 => 0x00000000
  | 10 => 0x00000001
  | 11 => 0x00000000
  | 12 => 0x00000001
  | 13 => 0x00000001
  | 14 => 0x00000001
  | 15 => 0x00000001
  | 16 => 0x00000000
  | 17 => 0x00000000
  | 18 => 0x00000000
  | 19 => 0x00000000
  | 20 => 0x00000001
  | 21 => 0x00000000
  | 22 => 0x00000001
  | 23 => 0x00000000
  | _ => 0

def rcO : UInt32 → UInt32
  | 0 => 0x00000000
  | 1 => 0x00000089
  | 2 => 0x8000008B
  | 3 => 0x80008080
  | 4 => 0x0000008B
  | 5 => 0x00008000
  | 6 => 0x80008088
  | 7 => 0x80000082
  | 8 => 0x0000000B
  | 9 => 0x0000000A
  | 10 => 0x00008082
  | 11 => 0x00008003
  | 12 => 0x0000808B
  | 13 => 0x8000000B
  | 14 => 0x8000008A
  | 15 => 0x80000081
  | 16 => 0x80000081
  | 17 => 0x80000008
  | 18 => 0x00000083
  | 19 => 0x80008003
  | 20 => 0x80008088
  | 21 => 0x80000088
  | 22 => 0x00008000
  | 23 => 0x80008082
  | _ => 0

/-- `2n` more rounds from round `i`, two per tail call, on the interleaved lanes. -/
def loopI2 : Nat → UInt32 → (a0e a0o a1e a1o a2e a2o a3e a3o a4e a4o a5e a5o a6e a6o a7e a7o a8e a8o a9e a9o a10e a10o a11e a11o a12e a12o a13e a13o a14e a14o a15e a15o a16e a16o a17e a17o a18e a18o a19e a19o a20e a20o a21e a21o a22e a22o a23e a23o a24e a24o : UInt32) → StateI
  | 0, _, a0e, a0o, a1e, a1o, a2e, a2o, a3e, a3o, a4e, a4o, a5e, a5o, a6e, a6o, a7e, a7o, a8e, a8o, a9e, a9o, a10e, a10o, a11e, a11o, a12e, a12o, a13e, a13o, a14e, a14o, a15e, a15o, a16e, a16o, a17e, a17o, a18e, a18o, a19e, a19o, a20e, a20o, a21e, a21o, a22e, a22o, a23e, a23o, a24e, a24o => ⟨a0e, a0o, a1e, a1o, a2e, a2o, a3e, a3o, a4e, a4o, a5e, a5o, a6e, a6o, a7e, a7o, a8e, a8o, a9e, a9o, a10e, a10o, a11e, a11o, a12e, a12o, a13e, a13o, a14e, a14o, a15e, a15o, a16e, a16o, a17e, a17o, a18e, a18o, a19e, a19o, a20e, a20o, a21e, a21o, a22e, a22o, a23e, a23o, a24e, a24o⟩
  | n + 1, i, a0e, a0o, a1e, a1o, a2e, a2o, a3e, a3o, a4e, a4o, a5e, a5o, a6e, a6o, a7e, a7o, a8e, a8o, a9e, a9o, a10e, a10o, a11e, a11o, a12e, a12o, a13e, a13o, a14e, a14o, a15e, a15o, a16e, a16o, a17e, a17o, a18e, a18o, a19e, a19o, a20e, a20o, a21e, a21o, a22e, a22o, a23e, a23o, a24e, a24o =>
    let c0e_0 := a0e ^^^ a5e ^^^ a10e ^^^ a15e ^^^ a20e
    let c1e_0 := a1e ^^^ a6e ^^^ a11e ^^^ a16e ^^^ a21e
    let c2e_0 := a2e ^^^ a7e ^^^ a12e ^^^ a17e ^^^ a22e
    let c3e_0 := a3e ^^^ a8e ^^^ a13e ^^^ a18e ^^^ a23e
    let c4e_0 := a4e ^^^ a9e ^^^ a14e ^^^ a19e ^^^ a24e
    let c0o_0 := a0o ^^^ a5o ^^^ a10o ^^^ a15o ^^^ a20o
    let c1o_0 := a1o ^^^ a6o ^^^ a11o ^^^ a16o ^^^ a21o
    let c2o_0 := a2o ^^^ a7o ^^^ a12o ^^^ a17o ^^^ a22o
    let c3o_0 := a3o ^^^ a8o ^^^ a13o ^^^ a18o ^^^ a23o
    let c4o_0 := a4o ^^^ a9o ^^^ a14o ^^^ a19o ^^^ a24o
    let d0e_0 := c4e_0 ^^^ rol32 c1o_0 1
    let d0o_0 := c4o_0 ^^^ c1e_0
    let d1e_0 := c0e_0 ^^^ rol32 c2o_0 1
    let d1o_0 := c0o_0 ^^^ c2e_0
    let d2e_0 := c1e_0 ^^^ rol32 c3o_0 1
    let d2o_0 := c1o_0 ^^^ c3e_0
    let d3e_0 := c2e_0 ^^^ rol32 c4o_0 1
    let d3o_0 := c2o_0 ^^^ c4e_0
    let d4e_0 := c3e_0 ^^^ rol32 c0o_0 1
    let d4o_0 := c3o_0 ^^^ c0e_0
    let r0e_0 := (a0e ^^^ d0e_0)
    let r0o_0 := (a0o ^^^ d0o_0)
    let r1e_0 := rol32 (a1o ^^^ d1o_0) 1
    let r1o_0 := (a1e ^^^ d1e_0)
    let r2e_0 := rol32 (a2e ^^^ d2e_0) 31
    let r2o_0 := rol32 (a2o ^^^ d2o_0) 31
    let r3e_0 := rol32 (a3e ^^^ d3e_0) 14
    let r3o_0 := rol32 (a3o ^^^ d3o_0) 14
    let r4e_0 := rol32 (a4o ^^^ d4o_0) 14
    let r4o_0 := rol32 (a4e ^^^ d4e_0) 13
    let r5e_0 := rol32 (a5e ^^^ d0e_0) 18
    let r5o_0 := rol32 (a5o ^^^ d0o_0) 18
    let r6e_0 := rol32 (a6e ^^^ d1e_0) 22
    let r6o_0 := rol32 (a6o ^^^ d1o_0) 22
    let r7e_0 := rol32 (a7e ^^^ d2e_0) 3
    let r7o_0 := rol32 (a7o ^^^ d2o_0) 3
    let r8e_0 := rol32 (a8o ^^^ d3o_0) 28
    let r8o_0 := rol32 (a8e ^^^ d3e_0) 27
    let r9e_0 := rol32 (a9e ^^^ d4e_0) 10
    let r9o_0 := rol32 (a9o ^^^ d4o_0) 10
    let r10e_0 := rol32 (a10o ^^^ d0o_0) 2
    let r10o_0 := rol32 (a10e ^^^ d0e_0) 1
    let r11e_0 := rol32 (a11e ^^^ d1e_0) 5
    let r11o_0 := rol32 (a11o ^^^ d1o_0) 5
    let r12e_0 := rol32 (a12o ^^^ d2o_0) 22
    let r12o_0 := rol32 (a12e ^^^ d2e_0) 21
    let r13e_0 := rol32 (a13o ^^^ d3o_0) 13
    let r13o_0 := rol32 (a13e ^^^ d3e_0) 12
    let r14e_0 := rol32 (a14o ^^^ d4o_0) 20
    let r14o_0 := rol32 (a14e ^^^ d4e_0) 19
    let r15e_0 := rol32 (a15o ^^^ d0o_0) 21
    let r15o_0 := rol32 (a15e ^^^ d0e_0) 20
    let r16e_0 := rol32 (a16o ^^^ d1o_0) 23
    let r16o_0 := rol32 (a16e ^^^ d1e_0) 22
    let r17e_0 := rol32 (a17o ^^^ d2o_0) 8
    let r17o_0 := rol32 (a17e ^^^ d2e_0) 7
    let r18e_0 := rol32 (a18o ^^^ d3o_0) 11
    let r18o_0 := rol32 (a18e ^^^ d3e_0) 10
    let r19e_0 := rol32 (a19e ^^^ d4e_0) 4
    let r19o_0 := rol32 (a19o ^^^ d4o_0) 4
    let r20e_0 := rol32 (a20e ^^^ d0e_0) 9
    let r20o_0 := rol32 (a20o ^^^ d0o_0) 9
    let r21e_0 := rol32 (a21e ^^^ d1e_0) 1
    let r21o_0 := rol32 (a21o ^^^ d1o_0) 1
    let r22e_0 := rol32 (a22o ^^^ d2o_0) 31
    let r22o_0 := rol32 (a22e ^^^ d2e_0) 30
    let r23e_0 := rol32 (a23e ^^^ d3e_0) 28
    let r23o_0 := rol32 (a23o ^^^ d3o_0) 28
    let r24e_0 := rol32 (a24e ^^^ d4e_0) 7
    let r24o_0 := rol32 (a24o ^^^ d4o_0) 7
    let b0e := (r0e_0 ^^^ (~~~r6e_0 &&& r12e_0)) ^^^ rcE i
    let b1e := r6e_0 ^^^ (~~~r12e_0 &&& r18e_0)
    let b2e := r12e_0 ^^^ (~~~r18e_0 &&& r24e_0)
    let b3e := r18e_0 ^^^ (~~~r24e_0 &&& r0e_0)
    let b4e := r24e_0 ^^^ (~~~r0e_0 &&& r6e_0)
    let b5e := r3e_0 ^^^ (~~~r9e_0 &&& r10e_0)
    let b6e := r9e_0 ^^^ (~~~r10e_0 &&& r16e_0)
    let b7e := r10e_0 ^^^ (~~~r16e_0 &&& r22e_0)
    let b8e := r16e_0 ^^^ (~~~r22e_0 &&& r3e_0)
    let b9e := r22e_0 ^^^ (~~~r3e_0 &&& r9e_0)
    let b10e := r1e_0 ^^^ (~~~r7e_0 &&& r13e_0)
    let b11e := r7e_0 ^^^ (~~~r13e_0 &&& r19e_0)
    let b12e := r13e_0 ^^^ (~~~r19e_0 &&& r20e_0)
    let b13e := r19e_0 ^^^ (~~~r20e_0 &&& r1e_0)
    let b14e := r20e_0 ^^^ (~~~r1e_0 &&& r7e_0)
    let b15e := r4e_0 ^^^ (~~~r5e_0 &&& r11e_0)
    let b16e := r5e_0 ^^^ (~~~r11e_0 &&& r17e_0)
    let b17e := r11e_0 ^^^ (~~~r17e_0 &&& r23e_0)
    let b18e := r17e_0 ^^^ (~~~r23e_0 &&& r4e_0)
    let b19e := r23e_0 ^^^ (~~~r4e_0 &&& r5e_0)
    let b20e := r2e_0 ^^^ (~~~r8e_0 &&& r14e_0)
    let b21e := r8e_0 ^^^ (~~~r14e_0 &&& r15e_0)
    let b22e := r14e_0 ^^^ (~~~r15e_0 &&& r21e_0)
    let b23e := r15e_0 ^^^ (~~~r21e_0 &&& r2e_0)
    let b24e := r21e_0 ^^^ (~~~r2e_0 &&& r8e_0)
    let b0o := (r0o_0 ^^^ (~~~r6o_0 &&& r12o_0)) ^^^ rcO i
    let b1o := r6o_0 ^^^ (~~~r12o_0 &&& r18o_0)
    let b2o := r12o_0 ^^^ (~~~r18o_0 &&& r24o_0)
    let b3o := r18o_0 ^^^ (~~~r24o_0 &&& r0o_0)
    let b4o := r24o_0 ^^^ (~~~r0o_0 &&& r6o_0)
    let b5o := r3o_0 ^^^ (~~~r9o_0 &&& r10o_0)
    let b6o := r9o_0 ^^^ (~~~r10o_0 &&& r16o_0)
    let b7o := r10o_0 ^^^ (~~~r16o_0 &&& r22o_0)
    let b8o := r16o_0 ^^^ (~~~r22o_0 &&& r3o_0)
    let b9o := r22o_0 ^^^ (~~~r3o_0 &&& r9o_0)
    let b10o := r1o_0 ^^^ (~~~r7o_0 &&& r13o_0)
    let b11o := r7o_0 ^^^ (~~~r13o_0 &&& r19o_0)
    let b12o := r13o_0 ^^^ (~~~r19o_0 &&& r20o_0)
    let b13o := r19o_0 ^^^ (~~~r20o_0 &&& r1o_0)
    let b14o := r20o_0 ^^^ (~~~r1o_0 &&& r7o_0)
    let b15o := r4o_0 ^^^ (~~~r5o_0 &&& r11o_0)
    let b16o := r5o_0 ^^^ (~~~r11o_0 &&& r17o_0)
    let b17o := r11o_0 ^^^ (~~~r17o_0 &&& r23o_0)
    let b18o := r17o_0 ^^^ (~~~r23o_0 &&& r4o_0)
    let b19o := r23o_0 ^^^ (~~~r4o_0 &&& r5o_0)
    let b20o := r2o_0 ^^^ (~~~r8o_0 &&& r14o_0)
    let b21o := r8o_0 ^^^ (~~~r14o_0 &&& r15o_0)
    let b22o := r14o_0 ^^^ (~~~r15o_0 &&& r21o_0)
    let b23o := r15o_0 ^^^ (~~~r21o_0 &&& r2o_0)
    let b24o := r21o_0 ^^^ (~~~r2o_0 &&& r8o_0)
    let c0e_1 := b0e ^^^ b5e ^^^ b10e ^^^ b15e ^^^ b20e
    let c1e_1 := b1e ^^^ b6e ^^^ b11e ^^^ b16e ^^^ b21e
    let c2e_1 := b2e ^^^ b7e ^^^ b12e ^^^ b17e ^^^ b22e
    let c3e_1 := b3e ^^^ b8e ^^^ b13e ^^^ b18e ^^^ b23e
    let c4e_1 := b4e ^^^ b9e ^^^ b14e ^^^ b19e ^^^ b24e
    let c0o_1 := b0o ^^^ b5o ^^^ b10o ^^^ b15o ^^^ b20o
    let c1o_1 := b1o ^^^ b6o ^^^ b11o ^^^ b16o ^^^ b21o
    let c2o_1 := b2o ^^^ b7o ^^^ b12o ^^^ b17o ^^^ b22o
    let c3o_1 := b3o ^^^ b8o ^^^ b13o ^^^ b18o ^^^ b23o
    let c4o_1 := b4o ^^^ b9o ^^^ b14o ^^^ b19o ^^^ b24o
    let d0e_1 := c4e_1 ^^^ rol32 c1o_1 1
    let d0o_1 := c4o_1 ^^^ c1e_1
    let d1e_1 := c0e_1 ^^^ rol32 c2o_1 1
    let d1o_1 := c0o_1 ^^^ c2e_1
    let d2e_1 := c1e_1 ^^^ rol32 c3o_1 1
    let d2o_1 := c1o_1 ^^^ c3e_1
    let d3e_1 := c2e_1 ^^^ rol32 c4o_1 1
    let d3o_1 := c2o_1 ^^^ c4e_1
    let d4e_1 := c3e_1 ^^^ rol32 c0o_1 1
    let d4o_1 := c3o_1 ^^^ c0e_1
    let r0e_1 := (b0e ^^^ d0e_1)
    let r0o_1 := (b0o ^^^ d0o_1)
    let r1e_1 := rol32 (b1o ^^^ d1o_1) 1
    let r1o_1 := (b1e ^^^ d1e_1)
    let r2e_1 := rol32 (b2e ^^^ d2e_1) 31
    let r2o_1 := rol32 (b2o ^^^ d2o_1) 31
    let r3e_1 := rol32 (b3e ^^^ d3e_1) 14
    let r3o_1 := rol32 (b3o ^^^ d3o_1) 14
    let r4e_1 := rol32 (b4o ^^^ d4o_1) 14
    let r4o_1 := rol32 (b4e ^^^ d4e_1) 13
    let r5e_1 := rol32 (b5e ^^^ d0e_1) 18
    let r5o_1 := rol32 (b5o ^^^ d0o_1) 18
    let r6e_1 := rol32 (b6e ^^^ d1e_1) 22
    let r6o_1 := rol32 (b6o ^^^ d1o_1) 22
    let r7e_1 := rol32 (b7e ^^^ d2e_1) 3
    let r7o_1 := rol32 (b7o ^^^ d2o_1) 3
    let r8e_1 := rol32 (b8o ^^^ d3o_1) 28
    let r8o_1 := rol32 (b8e ^^^ d3e_1) 27
    let r9e_1 := rol32 (b9e ^^^ d4e_1) 10
    let r9o_1 := rol32 (b9o ^^^ d4o_1) 10
    let r10e_1 := rol32 (b10o ^^^ d0o_1) 2
    let r10o_1 := rol32 (b10e ^^^ d0e_1) 1
    let r11e_1 := rol32 (b11e ^^^ d1e_1) 5
    let r11o_1 := rol32 (b11o ^^^ d1o_1) 5
    let r12e_1 := rol32 (b12o ^^^ d2o_1) 22
    let r12o_1 := rol32 (b12e ^^^ d2e_1) 21
    let r13e_1 := rol32 (b13o ^^^ d3o_1) 13
    let r13o_1 := rol32 (b13e ^^^ d3e_1) 12
    let r14e_1 := rol32 (b14o ^^^ d4o_1) 20
    let r14o_1 := rol32 (b14e ^^^ d4e_1) 19
    let r15e_1 := rol32 (b15o ^^^ d0o_1) 21
    let r15o_1 := rol32 (b15e ^^^ d0e_1) 20
    let r16e_1 := rol32 (b16o ^^^ d1o_1) 23
    let r16o_1 := rol32 (b16e ^^^ d1e_1) 22
    let r17e_1 := rol32 (b17o ^^^ d2o_1) 8
    let r17o_1 := rol32 (b17e ^^^ d2e_1) 7
    let r18e_1 := rol32 (b18o ^^^ d3o_1) 11
    let r18o_1 := rol32 (b18e ^^^ d3e_1) 10
    let r19e_1 := rol32 (b19e ^^^ d4e_1) 4
    let r19o_1 := rol32 (b19o ^^^ d4o_1) 4
    let r20e_1 := rol32 (b20e ^^^ d0e_1) 9
    let r20o_1 := rol32 (b20o ^^^ d0o_1) 9
    let r21e_1 := rol32 (b21e ^^^ d1e_1) 1
    let r21o_1 := rol32 (b21o ^^^ d1o_1) 1
    let r22e_1 := rol32 (b22o ^^^ d2o_1) 31
    let r22o_1 := rol32 (b22e ^^^ d2e_1) 30
    let r23e_1 := rol32 (b23e ^^^ d3e_1) 28
    let r23o_1 := rol32 (b23o ^^^ d3o_1) 28
    let r24e_1 := rol32 (b24e ^^^ d4e_1) 7
    let r24o_1 := rol32 (b24o ^^^ d4o_1) 7
    let z0e := (r0e_1 ^^^ (~~~r6e_1 &&& r12e_1)) ^^^ rcE (i + 1)
    let z1e := r6e_1 ^^^ (~~~r12e_1 &&& r18e_1)
    let z2e := r12e_1 ^^^ (~~~r18e_1 &&& r24e_1)
    let z3e := r18e_1 ^^^ (~~~r24e_1 &&& r0e_1)
    let z4e := r24e_1 ^^^ (~~~r0e_1 &&& r6e_1)
    let z5e := r3e_1 ^^^ (~~~r9e_1 &&& r10e_1)
    let z6e := r9e_1 ^^^ (~~~r10e_1 &&& r16e_1)
    let z7e := r10e_1 ^^^ (~~~r16e_1 &&& r22e_1)
    let z8e := r16e_1 ^^^ (~~~r22e_1 &&& r3e_1)
    let z9e := r22e_1 ^^^ (~~~r3e_1 &&& r9e_1)
    let z10e := r1e_1 ^^^ (~~~r7e_1 &&& r13e_1)
    let z11e := r7e_1 ^^^ (~~~r13e_1 &&& r19e_1)
    let z12e := r13e_1 ^^^ (~~~r19e_1 &&& r20e_1)
    let z13e := r19e_1 ^^^ (~~~r20e_1 &&& r1e_1)
    let z14e := r20e_1 ^^^ (~~~r1e_1 &&& r7e_1)
    let z15e := r4e_1 ^^^ (~~~r5e_1 &&& r11e_1)
    let z16e := r5e_1 ^^^ (~~~r11e_1 &&& r17e_1)
    let z17e := r11e_1 ^^^ (~~~r17e_1 &&& r23e_1)
    let z18e := r17e_1 ^^^ (~~~r23e_1 &&& r4e_1)
    let z19e := r23e_1 ^^^ (~~~r4e_1 &&& r5e_1)
    let z20e := r2e_1 ^^^ (~~~r8e_1 &&& r14e_1)
    let z21e := r8e_1 ^^^ (~~~r14e_1 &&& r15e_1)
    let z22e := r14e_1 ^^^ (~~~r15e_1 &&& r21e_1)
    let z23e := r15e_1 ^^^ (~~~r21e_1 &&& r2e_1)
    let z24e := r21e_1 ^^^ (~~~r2e_1 &&& r8e_1)
    let z0o := (r0o_1 ^^^ (~~~r6o_1 &&& r12o_1)) ^^^ rcO (i + 1)
    let z1o := r6o_1 ^^^ (~~~r12o_1 &&& r18o_1)
    let z2o := r12o_1 ^^^ (~~~r18o_1 &&& r24o_1)
    let z3o := r18o_1 ^^^ (~~~r24o_1 &&& r0o_1)
    let z4o := r24o_1 ^^^ (~~~r0o_1 &&& r6o_1)
    let z5o := r3o_1 ^^^ (~~~r9o_1 &&& r10o_1)
    let z6o := r9o_1 ^^^ (~~~r10o_1 &&& r16o_1)
    let z7o := r10o_1 ^^^ (~~~r16o_1 &&& r22o_1)
    let z8o := r16o_1 ^^^ (~~~r22o_1 &&& r3o_1)
    let z9o := r22o_1 ^^^ (~~~r3o_1 &&& r9o_1)
    let z10o := r1o_1 ^^^ (~~~r7o_1 &&& r13o_1)
    let z11o := r7o_1 ^^^ (~~~r13o_1 &&& r19o_1)
    let z12o := r13o_1 ^^^ (~~~r19o_1 &&& r20o_1)
    let z13o := r19o_1 ^^^ (~~~r20o_1 &&& r1o_1)
    let z14o := r20o_1 ^^^ (~~~r1o_1 &&& r7o_1)
    let z15o := r4o_1 ^^^ (~~~r5o_1 &&& r11o_1)
    let z16o := r5o_1 ^^^ (~~~r11o_1 &&& r17o_1)
    let z17o := r11o_1 ^^^ (~~~r17o_1 &&& r23o_1)
    let z18o := r17o_1 ^^^ (~~~r23o_1 &&& r4o_1)
    let z19o := r23o_1 ^^^ (~~~r4o_1 &&& r5o_1)
    let z20o := r2o_1 ^^^ (~~~r8o_1 &&& r14o_1)
    let z21o := r8o_1 ^^^ (~~~r14o_1 &&& r15o_1)
    let z22o := r14o_1 ^^^ (~~~r15o_1 &&& r21o_1)
    let z23o := r15o_1 ^^^ (~~~r21o_1 &&& r2o_1)
    let z24o := r21o_1 ^^^ (~~~r2o_1 &&& r8o_1)
    loopI2 n (i + 2) z0e z0o z1e z1o z2e z2o z3e z3o z4e z4o z5e z5o z6e z6o z7e z7o z8e z8o z9e z9o z10e z10o z11e z11o z12e z12o z13e z13o z14e z14o z15e z15o z16e z16o z17e z17o z18e z18o z19e z19o z20e z20o z21e z21o z22e z22o z23e z23o z24e z24o

/-- Keccak-f[1600] on the interleaved state. -/
def keccakPI (S : StateI) : StateI :=
  loopI2 12 0 S.e0 S.o0 S.e1 S.o1 S.e2 S.o2 S.e3 S.o3 S.e4 S.o4 S.e5 S.o5 S.e6 S.o6 S.e7 S.o7 S.e8 S.o8 S.e9 S.o9 S.e10 S.o10 S.e11 S.o11 S.e12 S.o12 S.e13 S.o13 S.e14 S.o14 S.e15 S.o15 S.e16 S.o16 S.e17 S.o17 S.e18 S.o18 S.e19 S.o19 S.e20 S.o20 S.e21 S.o21 S.e22 S.o22 S.e23 S.o23 S.e24 S.o24

/-- The even bits of the 64-bit lane `hi:lo`, compressed into a word. -/
@[inline] def shuf (x : UInt32) : UInt32 :=
  let t := (x ^^^ (x >>> 1)) &&& 0x22222222
  let x := x ^^^ t ^^^ (t <<< 1)
  let t := (x ^^^ (x >>> 2)) &&& 0x0C0C0C0C
  let x := x ^^^ t ^^^ (t <<< 2)
  let t := (x ^^^ (x >>> 4)) &&& 0x00F000F0
  let x := x ^^^ t ^^^ (t <<< 4)
  let t := (x ^^^ (x >>> 8)) &&& 0x0000FF00
  x ^^^ t ^^^ (t <<< 8)

/-- The inverse of `shuf`: the same delta swaps in reverse order. -/
@[inline] def unshuf (x : UInt32) : UInt32 :=
  let t := (x ^^^ (x >>> 8)) &&& 0x0000FF00
  let x := x ^^^ t ^^^ (t <<< 8)
  let t := (x ^^^ (x >>> 4)) &&& 0x00F000F0
  let x := x ^^^ t ^^^ (t <<< 4)
  let t := (x ^^^ (x >>> 2)) &&& 0x0C0C0C0C
  let x := x ^^^ t ^^^ (t <<< 2)
  let t := (x ^^^ (x >>> 1)) &&& 0x22222222
  x ^^^ t ^^^ (t <<< 1)

@[inline] def ilvE (lo hi : UInt32) : UInt32 := (shuf lo &&& (0xFFFF : UInt32)) ||| (shuf hi <<< 16)
@[inline] def ilvO (lo hi : UInt32) : UInt32 := (shuf lo >>> 16) ||| (shuf hi &&& (0xFFFF0000 : UInt32))
@[inline] def dlvLo (e o : UInt32) : UInt32 := unshuf ((e &&& (0xFFFF : UInt32)) ||| (o <<< 16))
@[inline] def dlvHi (e o : UInt32) : UInt32 := unshuf ((e >>> 16) ||| (o &&& (0xFFFF0000 : UInt32)))
@[inline] def ilvE64 (v : UInt64) : UInt32 := ilvE v.toUInt32 (v >>> 32).toUInt32
@[inline] def ilvO64 (v : UInt64) : UInt32 := ilvO v.toUInt32 (v >>> 32).toUInt32
@[inline] def dlv64 (e o : UInt32) : UInt64 := (dlvLo e o).toUInt64 ||| ((dlvHi e o).toUInt64 <<< 32)

/-- Absorb `n` blocks of 136 bytes from `p` on into the interleaved state. -/
def absorbI (bytes : @& ByteArray) : (n p : Nat) → p + 136 * n ≤ bytes.size → StateI → StateI
  | 0, _, _, S => S
  | n + 1, p, hp, S =>
    have h : p + 136 ≤ bytes.size := by omega
    let q := USize.ofNat p
    absorbI bytes n (p + 136) (by omega) (keccakPI ⟨
      S.e0 ^^^ ilvE (lane32 bytes p h q rfl 0 (by decide)) (lane32 bytes p h q rfl 4 (by decide)), S.o0 ^^^ ilvO (lane32 bytes p h q rfl 0 (by decide)) (lane32 bytes p h q rfl 4 (by decide)),
      S.e1 ^^^ ilvE (lane32 bytes p h q rfl 8 (by decide)) (lane32 bytes p h q rfl 12 (by decide)), S.o1 ^^^ ilvO (lane32 bytes p h q rfl 8 (by decide)) (lane32 bytes p h q rfl 12 (by decide)),
      S.e2 ^^^ ilvE (lane32 bytes p h q rfl 16 (by decide)) (lane32 bytes p h q rfl 20 (by decide)), S.o2 ^^^ ilvO (lane32 bytes p h q rfl 16 (by decide)) (lane32 bytes p h q rfl 20 (by decide)),
      S.e3 ^^^ ilvE (lane32 bytes p h q rfl 24 (by decide)) (lane32 bytes p h q rfl 28 (by decide)), S.o3 ^^^ ilvO (lane32 bytes p h q rfl 24 (by decide)) (lane32 bytes p h q rfl 28 (by decide)),
      S.e4 ^^^ ilvE (lane32 bytes p h q rfl 32 (by decide)) (lane32 bytes p h q rfl 36 (by decide)), S.o4 ^^^ ilvO (lane32 bytes p h q rfl 32 (by decide)) (lane32 bytes p h q rfl 36 (by decide)),
      S.e5 ^^^ ilvE (lane32 bytes p h q rfl 40 (by decide)) (lane32 bytes p h q rfl 44 (by decide)), S.o5 ^^^ ilvO (lane32 bytes p h q rfl 40 (by decide)) (lane32 bytes p h q rfl 44 (by decide)),
      S.e6 ^^^ ilvE (lane32 bytes p h q rfl 48 (by decide)) (lane32 bytes p h q rfl 52 (by decide)), S.o6 ^^^ ilvO (lane32 bytes p h q rfl 48 (by decide)) (lane32 bytes p h q rfl 52 (by decide)),
      S.e7 ^^^ ilvE (lane32 bytes p h q rfl 56 (by decide)) (lane32 bytes p h q rfl 60 (by decide)), S.o7 ^^^ ilvO (lane32 bytes p h q rfl 56 (by decide)) (lane32 bytes p h q rfl 60 (by decide)),
      S.e8 ^^^ ilvE (lane32 bytes p h q rfl 64 (by decide)) (lane32 bytes p h q rfl 68 (by decide)), S.o8 ^^^ ilvO (lane32 bytes p h q rfl 64 (by decide)) (lane32 bytes p h q rfl 68 (by decide)),
      S.e9 ^^^ ilvE (lane32 bytes p h q rfl 72 (by decide)) (lane32 bytes p h q rfl 76 (by decide)), S.o9 ^^^ ilvO (lane32 bytes p h q rfl 72 (by decide)) (lane32 bytes p h q rfl 76 (by decide)),
      S.e10 ^^^ ilvE (lane32 bytes p h q rfl 80 (by decide)) (lane32 bytes p h q rfl 84 (by decide)), S.o10 ^^^ ilvO (lane32 bytes p h q rfl 80 (by decide)) (lane32 bytes p h q rfl 84 (by decide)),
      S.e11 ^^^ ilvE (lane32 bytes p h q rfl 88 (by decide)) (lane32 bytes p h q rfl 92 (by decide)), S.o11 ^^^ ilvO (lane32 bytes p h q rfl 88 (by decide)) (lane32 bytes p h q rfl 92 (by decide)),
      S.e12 ^^^ ilvE (lane32 bytes p h q rfl 96 (by decide)) (lane32 bytes p h q rfl 100 (by decide)), S.o12 ^^^ ilvO (lane32 bytes p h q rfl 96 (by decide)) (lane32 bytes p h q rfl 100 (by decide)),
      S.e13 ^^^ ilvE (lane32 bytes p h q rfl 104 (by decide)) (lane32 bytes p h q rfl 108 (by decide)), S.o13 ^^^ ilvO (lane32 bytes p h q rfl 104 (by decide)) (lane32 bytes p h q rfl 108 (by decide)),
      S.e14 ^^^ ilvE (lane32 bytes p h q rfl 112 (by decide)) (lane32 bytes p h q rfl 116 (by decide)), S.o14 ^^^ ilvO (lane32 bytes p h q rfl 112 (by decide)) (lane32 bytes p h q rfl 116 (by decide)),
      S.e15 ^^^ ilvE (lane32 bytes p h q rfl 120 (by decide)) (lane32 bytes p h q rfl 124 (by decide)), S.o15 ^^^ ilvO (lane32 bytes p h q rfl 120 (by decide)) (lane32 bytes p h q rfl 124 (by decide)),
      S.e16 ^^^ ilvE (lane32 bytes p h q rfl 128 (by decide)) (lane32 bytes p h q rfl 132 (by decide)), S.o16 ^^^ ilvO (lane32 bytes p h q rfl 128 (by decide)) (lane32 bytes p h q rfl 132 (by decide)),
      S.e17, S.o17, S.e18, S.o18, S.e19, S.o19, S.e20, S.o20, S.e21, S.o21, S.e22, S.o22, S.e23, S.o23, S.e24, S.o24⟩)

/-- The 32 digest bytes from interleaved lanes 0 to 3. -/
def squeezeI (S : StateI) : Vector UInt8 DIGEST_LEN :=
  let a0 := dlvLo S.e0 S.o0; let a1 := dlvHi S.e0 S.o0
  let b0 := dlvLo S.e1 S.o1; let b1 := dlvHi S.e1 S.o1
  let c0 := dlvLo S.e2 S.o2; let c1 := dlvHi S.e2 S.o2
  let d0 := dlvLo S.e3 S.o3; let d1 := dlvHi S.e3 S.o3
  ⟨#[(a0 >>> 0).toUInt8, (a0 >>> 8).toUInt8, (a0 >>> 16).toUInt8, (a0 >>> 24).toUInt8, (a1 >>> 0).toUInt8, (a1 >>> 8).toUInt8, (a1 >>> 16).toUInt8, (a1 >>> 24).toUInt8, (b0 >>> 0).toUInt8, (b0 >>> 8).toUInt8, (b0 >>> 16).toUInt8, (b0 >>> 24).toUInt8, (b1 >>> 0).toUInt8, (b1 >>> 8).toUInt8, (b1 >>> 16).toUInt8, (b1 >>> 24).toUInt8, (c0 >>> 0).toUInt8, (c0 >>> 8).toUInt8, (c0 >>> 16).toUInt8, (c0 >>> 24).toUInt8, (c1 >>> 0).toUInt8, (c1 >>> 8).toUInt8, (c1 >>> 16).toUInt8, (c1 >>> 24).toUInt8, (d0 >>> 0).toUInt8, (d0 >>> 8).toUInt8, (d0 >>> 16).toUInt8, (d0 >>> 24).toUInt8, (d1 >>> 0).toUInt8, (d1 >>> 8).toUInt8, (d1 >>> 16).toUInt8, (d1 >>> 24).toUInt8], rfl⟩

def zeroI : StateI := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Keccak-256 with the interleaved state kept across blocks. -/
def keccak256I (msg : ByteArray) : Vector UInt8 DIGEST_LEN :=
  let padded := padF msg
  squeezeI (absorbI padded (padded.size / 136) 0
    (by have := Nat.mul_div_le padded.size 136; omega) zeroI)

end EthLib.Cryptography.Hash.Keccak.Fast
