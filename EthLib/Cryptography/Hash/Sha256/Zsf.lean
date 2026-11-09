module

/-!
# SHA-256, zero-allocation form (ZSf)

The same function as `EthLib.Cryptography.Hash.Sha256.hash`, written for 32-bit targets (M33).

Every working word is an unboxed `UInt32` parameter of one tail-recursive loop `zloop`.

The message is read in place through `@&` borrows.

The digest is written into a caller-owned 32-byte buffer (`hashInto`).

So a call allocates nothing when that buffer is exclusive, and at most the 32-byte result otherwise.

This module does not import the specification (`Sha256/Spec.lean`).

The initial hash value and the round constants are literals here.

So no specification closed terms are built at module initialisation.

`Sha256/ZsfProof/Main.lean` proves `hashInto m out = Sha256.hash m` for every `m` and `out`.

It installs `hash = hashZ`, `hash32 = hash32Z` and `sha256 = hashZ` with `@[csimp]`.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Sha256.Zsf

/-- Rotation right by `n` bits, ROTR of FIPS 180-4 §3.2. -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Shift right by `n` bits, SHR of FIPS 180-4 §3.2. -/
@[inline] def shr (x : UInt32) (n : UInt32) : UInt32 := x >>> n

/-- Ch of FIPS 180-4 §4.1.2 (4.2): each bit of `y` where `x` is set, and of `z` where it is not. -/
@[inline] def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)

/-- Maj of FIPS 180-4 §4.1.2 (4.3): each bit that at least two of the three words share. -/
@[inline] def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Σ0 of FIPS 180-4 §4.1.2 (4.4). -/
@[inline] def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- Σ1 of FIPS 180-4 §4.1.2 (4.5). -/
@[inline] def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- σ0 of FIPS 180-4 §4.1.2 (4.6). -/
@[inline] def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ shr x 3

/-- σ1 of FIPS 180-4 §4.1.2 (4.7). -/
@[inline] def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ shr x 10

/-- Four bytes read as one big-endian word, FIPS 180-4 §3.1. -/
@[inline] def big32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32


def kAt : UInt32 → UInt32
  | 0 => 0x428a2f98
  | 1 => 0x71374491
  | 2 => 0xb5c0fbcf
  | 3 => 0xe9b5dba5
  | 4 => 0x3956c25b
  | 5 => 0x59f111f1
  | 6 => 0x923f82a4
  | 7 => 0xab1c5ed5
  | 8 => 0xd807aa98
  | 9 => 0x12835b01
  | 10 => 0x243185be
  | 11 => 0x550c7dc3
  | 12 => 0x72be5d74
  | 13 => 0x80deb1fe
  | 14 => 0x9bdc06a7
  | 15 => 0xc19bf174
  | 16 => 0xe49b69c1
  | 17 => 0xefbe4786
  | 18 => 0x0fc19dc6
  | 19 => 0x240ca1cc
  | 20 => 0x2de92c6f
  | 21 => 0x4a7484aa
  | 22 => 0x5cb0a9dc
  | 23 => 0x76f988da
  | 24 => 0x983e5152
  | 25 => 0xa831c66d
  | 26 => 0xb00327c8
  | 27 => 0xbf597fc7
  | 28 => 0xc6e00bf3
  | 29 => 0xd5a79147
  | 30 => 0x06ca6351
  | 31 => 0x14292967
  | 32 => 0x27b70a85
  | 33 => 0x2e1b2138
  | 34 => 0x4d2c6dfc
  | 35 => 0x53380d13
  | 36 => 0x650a7354
  | 37 => 0x766a0abb
  | 38 => 0x81c2c92e
  | 39 => 0x92722c85
  | 40 => 0xa2bfe8a1
  | 41 => 0xa81a664b
  | 42 => 0xc24b8b70
  | 43 => 0xc76c51a3
  | 44 => 0xd192e819
  | 45 => 0xd6990624
  | 46 => 0xf40e3585
  | 47 => 0x106aa070
  | 48 => 0x19a4c116
  | 49 => 0x1e376c08
  | 50 => 0x2748774c
  | 51 => 0x34b0bcb5
  | 52 => 0x391c0cb3
  | 53 => 0x4ed8aa4a
  | 54 => 0x5b9cca4f
  | 55 => 0x682e6ff3
  | 56 => 0x748f82ee
  | 57 => 0x78a5636f
  | 58 => 0x84c87814
  | 59 => 0x8cc70208
  | 60 => 0x90befffa
  | 61 => 0xa4506ceb
  | 62 => 0xbef9a3f7
  | 63 => 0xc67178f2
  | _ => 0

/-- Thirty-two zero bytes: the template the digest is written into (copied on the first write). -/
def zeros32 : ByteArray := ⟨Array.replicate 32 0⟩

theorem zeros32_size : zeros32.size = 32 := by simp [zeros32, ByteArray.size]

theorem size_set' (b : ByteArray) (i : Nat) (v : UInt8) (h : i < b.size) :
    (b.set i v h).size = b.size := by
  cases b; simp [ByteArray.set, ByteArray.size]

/-- Big-endian bytes of a word, written in place at offset `o`. -/
@[inline] def put32 (b : ByteArray) (o : Nat) (w : UInt32) (h : o + 4 ≤ b.size) : ByteArray :=
  (((b.set o (w >>> 24).toUInt8 (by omega)).set (o + 1) (w >>> 16).toUInt8
      (by rw [size_set']; omega)).set
    (o + 2) (w >>> 8).toUInt8 (by rw [size_set', size_set']; omega)).set (o + 3) w.toUInt8
    (by rw [size_set', size_set', size_set']; omega)

theorem size_put32 (b : ByteArray) (o : Nat) (w : UInt32) (h : o + 4 ≤ b.size) :
    (put32 b o w h).size = b.size := by
  simp only [put32, size_set']

/-- The `j`-th big-endian word of the block at `start`, exactly as `Window.ofBlock` reads it. -/
@[inline] def wordAt (bytes : @& ByteArray) (start j : Nat) (h : start + 4 * j + 3 < bytes.size) :
    UInt32 :=
  big32 (bytes[start + 4 * j]'(by omega)) (bytes[start + 4 * j + 1]'(by omega))
    (bytes[start + 4 * j + 2]'(by omega)) (bytes[start + 4 * j + 3]'(by omega))

/-! ## Padding without a copy: full blocks straight from the message, the last one or two
    blocks computed word by word from the message tail, the `0x80` byte, zeros and the length. -/

/-- Byte `start + i` of the message as a word. -/
@[inline] def mb (m : @& ByteArray) (start i : Nat) (h : start + i < m.size) : UInt32 :=
  (m[start + i]'h).toUInt32

-- (above doc) The word holding the 0x80 byte, out of line.
--
-- The caller folds `p = start + 4j` and `k = r - 4j < 4`.
--
-- So the function does no multiply and reads at most m[p], m[p+1], m[p+2].
@[noinline] def partialWord (m : @& ByteArray) (p k : Nat) (hp : p + k = m.size) (hk : k < 4) :
    UInt32 :=
  if h1 : k = 0 then 0x80000000
  else if h2 : k = 1 then (m[p]'(by omega)).toUInt32 <<< 24 ||| 0x800000
  else if h3 : k = 2 then
    (m[p]'(by omega)).toUInt32 <<< 24 ||| (m[p + 1]'(by omega)).toUInt32 <<< 16 ||| 0x8000
  else
    (m[p]'(by omega)).toUInt32 <<< 24 ||| (m[p + 1]'(by omega)).toUInt32 <<< 16 |||
      (m[p + 2]'(by omega)).toUInt32 <<< 8 ||| 0x80

/-- Word `j` of the padded tail.

Whole message words and zero words are inline, the one word with the `0x80` byte is `partialWord`.

Same value as the 6-case `tailWord` of A1. -/
@[inline] def tailWord (m : @& ByteArray) (start r j : Nat) (hr : start + r = m.size) : UInt32 :=
  if h : 4 * j + 4 ≤ r then wordAt m start j (by omega)
  else if h0 : r < 4 * j then 0
  else partialWord m (start + 4 * j) (r - 4 * j) (by omega) (by omega)

theorem usz_ge : 4294967296 ≤ 2 ^ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

/-- `USize` addition does not wrap below `2^32`. -/
theorem add_toNat (o k : USize) (h : o.toNat + k.toNat < 4294967296) :
    (o + k).toNat = o.toNat + k.toNat := by
  rw [USize.toNat_add]; have := usz_ge; apply Nat.mod_eq_of_lt; omega

/-- The big-endian word at byte offset `o`: four `uget`s, no `Nat` arithmetic. -/
@[inline] def wordU (bytes : @& ByteArray) (o : USize) (hb : o.toNat < 1073741888)
    (h : o.toNat + 3 < bytes.size) : UInt32 :=
  big32 (bytes.uget o (by omega))
    (bytes.uget (o + 1) (by rw [add_toNat o 1 (by simp; omega)]; simp; omega))
    (bytes.uget (o + 2) (by rw [add_toNat o 2 (by simp; omega)]; simp; omega))
    (bytes.uget (o + 3) (by rw [add_toNat o 3 (by simp; omega)]; simp; omega))

/-- `wordAt`, out of line: only the (>= 2^30-byte) fallback path uses it, so it is kept small. -/
@[noinline] def wordAtN (bytes : @& ByteArray) (start j : Nat)
    (h : start + 4 * j + 3 < bytes.size) : UInt32 :=
  wordAt bytes start j h

/-! ## Zero allocations: the whole hash is one tail-recursive loop (spec-free, compact tail) -/

/-- What follows the block in flight.

It is more message, one last zero-and-length block, or the digest. -/
inductive Ph | body | last | done

set_option maxRecDepth 8192


/-- `t < 64`: sixteen more rounds; `t ≥ 64`: feed-forward, then the next block or the digest.

The offset `s` is a `Nat`.

Full blocks of a message shorter than 2^30 bytes are read through `USize` (`wordU`).

Longer ones go through the out-of-line `wordAtN`, in the same loop, with no spec fallback. -/
def zloop (fuel : Nat) (m : @& ByteArray) (out : ByteArray) (hout : out.size = 32)
    (ph : Ph) (s : Nat) (ho : s ≤ m.size) (t : UInt32)
    (H0 H1 H2 H3 H4 H5 H6 H7 : UInt32) (a b c d e f g h : UInt32)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) : ByteArray :=
  match fuel with
  | 0 => out
  | fuel + 1 =>
  if ht : t < 64 then
    let t1_0 := h + bigSigma1 e + ch e f g + kAt (t + 0) + w0
    let t2_0 := bigSigma0 a + maj a b c
    let a0 := t1_0 + t2_0
    let e0 := d + t1_0
    let t1_1 := g + bigSigma1 e0 + ch e0 e f + kAt (t + 1) + w1
    let t2_1 := bigSigma0 a0 + maj a0 a b
    let a1 := t1_1 + t2_1
    let e1 := c + t1_1
    let t1_2 := f + bigSigma1 e1 + ch e1 e0 e + kAt (t + 2) + w2
    let t2_2 := bigSigma0 a1 + maj a1 a0 a
    let a2 := t1_2 + t2_2
    let e2 := b + t1_2
    let t1_3 := e + bigSigma1 e2 + ch e2 e1 e0 + kAt (t + 3) + w3
    let t2_3 := bigSigma0 a2 + maj a2 a1 a0
    let a3 := t1_3 + t2_3
    let e3 := a + t1_3
    let t1_4 := e0 + bigSigma1 e3 + ch e3 e2 e1 + kAt (t + 4) + w4
    let t2_4 := bigSigma0 a3 + maj a3 a2 a1
    let a4 := t1_4 + t2_4
    let e4 := a0 + t1_4
    let t1_5 := e1 + bigSigma1 e4 + ch e4 e3 e2 + kAt (t + 5) + w5
    let t2_5 := bigSigma0 a4 + maj a4 a3 a2
    let a5 := t1_5 + t2_5
    let e5 := a1 + t1_5
    let t1_6 := e2 + bigSigma1 e5 + ch e5 e4 e3 + kAt (t + 6) + w6
    let t2_6 := bigSigma0 a5 + maj a5 a4 a3
    let a6 := t1_6 + t2_6
    let e6 := a2 + t1_6
    let t1_7 := e3 + bigSigma1 e6 + ch e6 e5 e4 + kAt (t + 7) + w7
    let t2_7 := bigSigma0 a6 + maj a6 a5 a4
    let a7 := t1_7 + t2_7
    let e7 := a3 + t1_7
    let t1_8 := e4 + bigSigma1 e7 + ch e7 e6 e5 + kAt (t + 8) + w8
    let t2_8 := bigSigma0 a7 + maj a7 a6 a5
    let a8 := t1_8 + t2_8
    let e8 := a4 + t1_8
    let t1_9 := e5 + bigSigma1 e8 + ch e8 e7 e6 + kAt (t + 9) + w9
    let t2_9 := bigSigma0 a8 + maj a8 a7 a6
    let a9 := t1_9 + t2_9
    let e9 := a5 + t1_9
    let t1_10 := e6 + bigSigma1 e9 + ch e9 e8 e7 + kAt (t + 10) + w10
    let t2_10 := bigSigma0 a9 + maj a9 a8 a7
    let a10 := t1_10 + t2_10
    let e10 := a6 + t1_10
    let t1_11 := e7 + bigSigma1 e10 + ch e10 e9 e8 + kAt (t + 11) + w11
    let t2_11 := bigSigma0 a10 + maj a10 a9 a8
    let a11 := t1_11 + t2_11
    let e11 := a7 + t1_11
    let t1_12 := e8 + bigSigma1 e11 + ch e11 e10 e9 + kAt (t + 12) + w12
    let t2_12 := bigSigma0 a11 + maj a11 a10 a9
    let a12 := t1_12 + t2_12
    let e12 := a8 + t1_12
    let t1_13 := e9 + bigSigma1 e12 + ch e12 e11 e10 + kAt (t + 13) + w13
    let t2_13 := bigSigma0 a12 + maj a12 a11 a10
    let a13 := t1_13 + t2_13
    let e13 := a9 + t1_13
    let t1_14 := e10 + bigSigma1 e13 + ch e13 e12 e11 + kAt (t + 14) + w14
    let t2_14 := bigSigma0 a13 + maj a13 a12 a11
    let a14 := t1_14 + t2_14
    let e14 := a10 + t1_14
    let t1_15 := e11 + bigSigma1 e14 + ch e14 e13 e12 + kAt (t + 15) + w15
    let t2_15 := bigSigma0 a14 + maj a14 a13 a12
    let a15 := t1_15 + t2_15
    let e15 := a11 + t1_15
    if t < 48 then
      let x0 := w0 + smallSigma0 w1 + w9 + smallSigma1 w14
      let x1 := w1 + smallSigma0 w2 + w10 + smallSigma1 w15
      let x2 := w2 + smallSigma0 w3 + w11 + smallSigma1 x0
      let x3 := w3 + smallSigma0 w4 + w12 + smallSigma1 x1
      let x4 := w4 + smallSigma0 w5 + w13 + smallSigma1 x2
      let x5 := w5 + smallSigma0 w6 + w14 + smallSigma1 x3
      let x6 := w6 + smallSigma0 w7 + w15 + smallSigma1 x4
      let x7 := w7 + smallSigma0 w8 + x0 + smallSigma1 x5
      let x8 := w8 + smallSigma0 w9 + x1 + smallSigma1 x6
      let x9 := w9 + smallSigma0 w10 + x2 + smallSigma1 x7
      let x10 := w10 + smallSigma0 w11 + x3 + smallSigma1 x8
      let x11 := w11 + smallSigma0 w12 + x4 + smallSigma1 x9
      let x12 := w12 + smallSigma0 w13 + x5 + smallSigma1 x10
      let x13 := w13 + smallSigma0 w14 + x6 + smallSigma1 x11
      let x14 := w14 + smallSigma0 w15 + x7 + smallSigma1 x12
      let x15 := w15 + smallSigma0 x0 + x8 + smallSigma1 x13
      zloop fuel m out hout ph s ho (t + 16) H0 H1 H2 H3 H4 H5 H6 H7 a15 a14 a13 a12 e15 e14 e13 e12
        x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
    else
      zloop fuel m out hout ph s ho (t + 16) H0 H1 H2 H3 H4 H5 H6 H7 a15 a14 a13 a12 e15 e14 e13 e12
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
  else
    let A := H0 + a; let B := H1 + b; let C := H2 + c; let D := H3 + d
    let E := H4 + e; let F := H5 + f; let G := H6 + g; let H := H7 + h
    match ph with
    | .done =>
      put32 (put32 (put32 (put32 (put32 (put32 (put32 (put32 out
        0 A (by omega)) 4 B (by simp [size_put32]; omega))
        8 C (by simp [size_put32]; omega)) 12 D (by simp [size_put32]; omega))
        16 E (by simp [size_put32]; omega)) 20 F (by simp [size_put32]; omega))
        24 G (by simp [size_put32]; omega)) 28 H (by simp [size_put32]; omega)
    | .last =>
      let bits : UInt64 := UInt64.ofNat m.size * 8
      zloop fuel m out hout .done s ho 0 A B C D E F G H A B C D E F G H 0 0 0 0 0 0 0 0 0 0 0 0 0 0
          (bits >>> 32).toUInt32 bits.toUInt32
    | .body =>
      if hf : s + 64 ≤ m.size then
        if hs : m.size < 1073741824 then
          let o := s.toUInt32.toUSize
          have hoe : o.toNat = s := by simp [o, UInt32.toNat_toUSize]; omega
          zloop fuel m out hout .body (s + 64) (by omega) 0 A B C D E F G H A B C D E F G H
            (wordU m o (by omega) (by omega))
            (wordU m (o + 4) (by rw [add_toNat o 4 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 4 (by simp; omega)]; simp; omega))
            (wordU m (o + 8) (by rw [add_toNat o 8 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 8 (by simp; omega)]; simp; omega))
            (wordU m (o + 12) (by rw [add_toNat o 12 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 12 (by simp; omega)]; simp; omega))
            (wordU m (o + 16) (by rw [add_toNat o 16 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 16 (by simp; omega)]; simp; omega))
            (wordU m (o + 20) (by rw [add_toNat o 20 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 20 (by simp; omega)]; simp; omega))
            (wordU m (o + 24) (by rw [add_toNat o 24 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 24 (by simp; omega)]; simp; omega))
            (wordU m (o + 28) (by rw [add_toNat o 28 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 28 (by simp; omega)]; simp; omega))
            (wordU m (o + 32) (by rw [add_toNat o 32 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 32 (by simp; omega)]; simp; omega))
            (wordU m (o + 36) (by rw [add_toNat o 36 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 36 (by simp; omega)]; simp; omega))
            (wordU m (o + 40) (by rw [add_toNat o 40 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 40 (by simp; omega)]; simp; omega))
            (wordU m (o + 44) (by rw [add_toNat o 44 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 44 (by simp; omega)]; simp; omega))
            (wordU m (o + 48) (by rw [add_toNat o 48 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 48 (by simp; omega)]; simp; omega))
            (wordU m (o + 52) (by rw [add_toNat o 52 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 52 (by simp; omega)]; simp; omega))
            (wordU m (o + 56) (by rw [add_toNat o 56 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 56 (by simp; omega)]; simp; omega))
            (wordU m (o + 60) (by rw [add_toNat o 60 (by simp; omega)]; simp; omega)
                (by rw [add_toNat o 60 (by simp; omega)]; simp; omega))
        else
          zloop fuel m out hout .body (s + 64) (by omega) 0 A B C D E F G H A B C D E F G H
            (wordAtN m s 0 (by omega))
            (wordAtN m s 1 (by omega))
            (wordAtN m s 2 (by omega))
            (wordAtN m s 3 (by omega))
            (wordAtN m s 4 (by omega))
            (wordAtN m s 5 (by omega))
            (wordAtN m s 6 (by omega))
            (wordAtN m s 7 (by omega))
            (wordAtN m s 8 (by omega))
            (wordAtN m s 9 (by omega))
            (wordAtN m s 10 (by omega))
            (wordAtN m s 11 (by omega))
            (wordAtN m s 12 (by omega))
            (wordAtN m s 13 (by omega))
            (wordAtN m s 14 (by omega))
            (wordAtN m s 15 (by omega))
      else
        let r := m.size - s
        have hr : s + r = m.size := by omega
        let bits : UInt64 := UInt64.ofNat m.size * 8
        let w0 := tailWord m s r 0 hr
        let w1 := tailWord m s r 1 hr
        let w2 := tailWord m s r 2 hr
        let w3 := tailWord m s r 3 hr
        let w4 := tailWord m s r 4 hr
        let w5 := tailWord m s r 5 hr
        let w6 := tailWord m s r 6 hr
        let w7 := tailWord m s r 7 hr
        let w8 := tailWord m s r 8 hr
        let w9 := tailWord m s r 9 hr
        let w10 := tailWord m s r 10 hr
        let w11 := tailWord m s r 11 hr
        let w12 := tailWord m s r 12 hr
        let w13 := tailWord m s r 13 hr
        if r < 56 then
          zloop fuel m out hout .done s ho 0 A B C D E F G H A B C D E F G H
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (bits >>> 32).toUInt32 bits.toUInt32
        else
          zloop fuel m out hout .last s ho 0 A B C D E F G H A B C D E F G H
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (tailWord m s r 14 hr) (tailWord m s r 15
                hr)

/-- SHA-256 of `m`, written into `out`.

It writes in place when `out` is exclusive and 32 bytes, and otherwise into a fresh 32-byte buffer.
-/
def hashInto (m : @& ByteArray) (out : ByteArray) : ByteArray :=
  let out := if out.size = 32 then out else zeros32
  if hout : out.size = 32 then
    zloop (5 * (m.size / 64) + 16) m out hout .body 0 (Nat.zero_le _) 64
      0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a 0x510e527f 0x9b05688c 0x1f83d9ab 0x5be0cd19
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  else out

/-- SHA-256 of `m` into a fresh 32-byte buffer (one allocation: the result). -/
def hashZ (m : @& ByteArray) : ByteArray := hashInto m zeros32

end EthLib.Cryptography.Hash.Sha256.Zsf
