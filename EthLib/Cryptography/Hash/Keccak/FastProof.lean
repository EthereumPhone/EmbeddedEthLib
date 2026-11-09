module

public import EthLib.Cryptography.Hash.Keccak.Fast

/-! Proofs that the fast forms equal the spec, and the `@[csimp]` lemmas that install them.

- `keccakF1 = keccakF`, `keccakF2 = keccakF`; `@[csimp] keccakF = keccakF2`.
- `padF msg = pad RATE msg`, `absorbU = Internal.absorbBlocks` (arrays below `USize.size`).
  `keccak256U = keccak256`, no longer a `@[csimp]`.
  `FastProofI` installs the faster, also proved, bit-interleaved `keccak256IG` instead.
- `@[csimp]` copies of `keccak512`, `Hasher.absorb`, `Hasher.digest` (all `rfl`).
  They are recompiled here, so their `keccakF` call sites become `keccakF2`.

A csimp lemma rewrites only code compiled after it is in scope.

So a consumer must import this module, as `Sphincs.TweakableHash` does. -/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak.Fast
open EthLib.Cryptography.Hash.Keccak

theorem rcAt_eq : ∀ k : Fin 24, RC[k] = rcAt (UInt32.ofNat k.val) := by decide

theorem rc_of (i : UInt32) (h : i.toNat < ROUNDS) : RC[(⟨i.toNat, h⟩ : Fin ROUNDS)] = rcAt i := by
  have := rcAt_eq ⟨i.toNat, h⟩
  rw [UInt32.ofNat_toNat] at this
  exact this

theorem toNat_succ (i : UInt32) (h : i.toNat < 24) : (i + 1).toNat = i.toNat + 1 := by
  rw [UInt32.toNat_add]; simp; omega

theorem roundsFrom_succ (i : Nat) (h : i < 24) (A : State) :
    keccakF.roundsFrom i A = keccakF.roundsFrom (i + 1) (round ⟨i, h⟩ A) := by
  rw [keccakF.roundsFrom]; simp [ROUNDS, h]

theorem roundsFrom_24 (A : State) : keccakF.roundsFrom 24 A = A := by
  rw [keccakF.roundsFrom]; simp [ROUNDS]

theorem loop1_eq : ∀ (n : Nat) (i : UInt32) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64),
    i.toNat + n = 24 → loop1 n i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18
        a19 a20 a21 a22 a23 a24 = keccakF.roundsFrom i.toNat ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8,
        a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24⟩ := by
  intro n
  induction n with
  | zero =>
    intro i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
      a24 h
    simp at h; rw [h, roundsFrom_24]; rfl
  | succ n ih =>
    intro i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
        a24 h
    have hi : i.toNat < 24 := by omega
    rw [roundsFrom_succ _ hi]
    have hs := toNat_succ i hi
    have hr := rc_of i hi
    simp only [loop1]
    rw [ih (i + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega), hs]
    congr 1
    simp only [round, iota, chi, pi, rho, theta]
    rw [← hr]
    rfl

theorem keccakF1_eq : keccakF1 = keccakF := by
  funext A; cases A
  simp only [keccakF1, keccakF]
  exact loop1_eq 24 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)

theorem toNat_succ2 (i : UInt32) (h : i.toNat < 23) : (i + 1 + 1).toNat = i.toNat + 2 := by
  rw [UInt32.toNat_add, UInt32.toNat_add]; simp; omega

theorem toNat_add2 (i : UInt32) (h : i.toNat < 23) : (i + 2).toNat = i.toNat + 2 := by
  rw [UInt32.toNat_add]; simp; omega

theorem loop2_eq : ∀ (n : Nat) (i : UInt32) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64),
    i.toNat + 2 * n = 24 → loop2 n i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17
        a18 a19 a20 a21 a22 a23 a24 = keccakF.roundsFrom i.toNat ⟨a0, a1, a2, a3, a4, a5, a6, a7,
        a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24⟩ := by
  intro n
  induction n with
  | zero =>
    intro i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
      a24 h
    simp at h; rw [h, roundsFrom_24]; rfl
  | succ n ih =>
    intro i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
        a24 h
    have hi : i.toNat < 24 := by omega
    have hi1 : (i + 1).toNat < 24 := by rw [toNat_succ i hi]; omega
    rw [roundsFrom_succ _ hi, roundsFrom_succ _ (by omega)]
    have hr := rc_of i hi
    have hr1 := rc_of (i + 1) hi1
    simp only [loop2]
    rw [ih (i + 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (by rw [toNat_add2 i (by omega)]; omega), toNat_add2 i (by omega)]
    congr 1
    have e1 : i.toNat + 1 = (i + 1).toNat := (toNat_succ i hi).symm
    simp only [e1]
    simp only [round, iota, chi, pi, rho, theta]
    rw [← hr, ← hr1]
    rfl

theorem keccakF2_eq : keccakF2 = keccakF := by
  funext A; cases A
  simp only [keccakF2, keccakF]
  exact loop2_eq 12 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)

/-- Installs the two-rounds-per-call form for every call compiled after this module. -/
@[csimp] theorem keccakF_eq_keccakF2 : keccakF = keccakF2 := keccakF2_eq.symm


/-! ## A proved in-place sponge for Keccak-256

`absorbU` reads each lane with eight `ByteArray.uget`s at `USize` offsets.

It reads in the byte order of `Internal.laneAt`, so the proof needs only that each read is `byteAt`.

The index `q + c` is the true offset `p + c` when the array is shorter than `USize.size`.

`keccak256U` tests that once. -/

/-- Byte `c` of the block at `p`, read in place, as a lane. -/
@[inline] def rdU (bytes : @& ByteArray) (p : Nat) (h : p + 136 ≤ bytes.size) (q : USize)
    (hq : q = USize.ofNat p) (c : Nat) (hc : c < 136) : UInt64 :=
  (bytes.uget (q + USize.ofNat c) (hq ▸ idx_lt h c hc)).toUInt64

/-- The lane of bytes `c` to `c + 7` of the block at `p`, shaped like `Internal.laneAt`. -/
@[inline] def laneU (bytes : @& ByteArray) (_hs : bytes.size < USize.size) (p : Nat)
    (h : p + 136 ≤ bytes.size) (q : USize) (hq : q = USize.ofNat p) (c : Nat) (hc : c + 8 ≤ 136) :
    UInt64 :=
  rdU bytes p h q hq c (by omega) ||| rdU bytes p h q hq (c + 1) (by omega) <<< 8 |||
    rdU bytes p h q hq (c + 2) (by omega) <<< 16 |||
    rdU bytes p h q hq (c + 3) (by omega) <<< 24 |||
    rdU bytes p h q hq (c + 4) (by omega) <<< 32 |||
    rdU bytes p h q hq (c + 5) (by omega) <<< 40 |||
    rdU bytes p h q hq (c + 6) (by omega) <<< 48 |||
    rdU bytes p h q hq (c + 7) (by omega) <<< 56

/-- Absorb `n` blocks of 136 bytes from `p` on, the permutation `f` after each. -/
@[specialize] def absorbU (f : State → State) (bytes : @& ByteArray)
    (hs : bytes.size < USize.size) :
    (n p : Nat) → p + 136 * n ≤ bytes.size → State → State
  | 0, _, _, S => S
  | n + 1, p, hp, S =>
    have h : p + 136 ≤ bytes.size := by omega
    let q := USize.ofNat p
    absorbU f bytes hs n (p + 136) (by omega) (f ⟨
      S.a0 ^^^ laneU bytes hs p h q rfl 0 (by decide),
      S.a1 ^^^ laneU bytes hs p h q rfl 8 (by decide),
      S.a2 ^^^ laneU bytes hs p h q rfl 16 (by decide),
      S.a3 ^^^ laneU bytes hs p h q rfl 24 (by decide),
      S.a4 ^^^ laneU bytes hs p h q rfl 32 (by decide),
      S.a5 ^^^ laneU bytes hs p h q rfl 40 (by decide),
      S.a6 ^^^ laneU bytes hs p h q rfl 48 (by decide),
      S.a7 ^^^ laneU bytes hs p h q rfl 56 (by decide),
      S.a8 ^^^ laneU bytes hs p h q rfl 64 (by decide),
      S.a9 ^^^ laneU bytes hs p h q rfl 72 (by decide),
      S.a10 ^^^ laneU bytes hs p h q rfl 80 (by decide),
      S.a11 ^^^ laneU bytes hs p h q rfl 88 (by decide),
      S.a12 ^^^ laneU bytes hs p h q rfl 96 (by decide),
      S.a13 ^^^ laneU bytes hs p h q rfl 104 (by decide),
      S.a14 ^^^ laneU bytes hs p h q rfl 112 (by decide),
      S.a15 ^^^ laneU bytes hs p h q rfl 120 (by decide),
      S.a16 ^^^ laneU bytes hs p h q rfl 128 (by decide),
      S.a17, S.a18, S.a19, S.a20, S.a21, S.a22, S.a23, S.a24⟩)

/-- The padded length is the block count times the rate (`Proofs/Hash/Keccak.lean`, `size_pad`). -/
theorem size_padding' (rate len : Nat) : (padding rate len).size = rate - len % rate := by
  simp [padding, ByteArray.size]

theorem size_pad' {rate : Nat} (hr : 0 < rate) (msg : ByteArray) :
    (pad rate msg).size = rate * blockCount rate msg.size := by
  have hs : msg.size % rate < rate := Nat.mod_lt _ hr
  have hd := Nat.div_add_mod msg.size rate
  simp only [pad, ByteArray.size_append, size_padding', blockCount]
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ### `padF = pad RATE` -/

theorem zeros_extract (k : Nat) (hk : k ≤ 136) :
    zeros136.extract 0 (0 + k) = ⟨Array.replicate k 0⟩ := by
  apply ByteArray.ext
  simp [zeros136, ByteArray.data_extract]
  omega

theorem copy_eq (msg : ByteArray) (k : Nat) (hk : k ≤ 136) :
    zeros136.copySlice 0 msg msg.size k = msg ++ ⟨Array.replicate k 0⟩ := by
  rw [ByteArray.copySlice_eq_append, zeros_extract k hk, ByteArray.extract_zero_size]
  have : msg.extract (msg.size + min k (zeros136.data.size - 0)) msg.data.size =
      ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff]; simp only [zeros136, Array.size_replicate]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_add_right _ _)
  rw [this]
  apply ByteArray.ext; simp

theorem app_eq (msg : ByteArray) (c : Nat) : (ByteArray.emptyWithCapacity c).append msg = msg := by
  apply ByteArray.ext
  rfl


theorem get!_of_lt (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b[i] := by
  cases b with
  | mk bs =>
    show bs[i]! = bs[i]'h
    exact getElem!_pos bs i h

theorem size_mk (a : Array UInt8) : ({ data := a } : ByteArray).size = a.size := rfl

theorem getElem_mk (a : Array UInt8) (i : Nat) (h : i < ({ data := a } : ByteArray).size) :
    ({ data := a } : ByteArray)[i] = a[i]'h := rfl

open Internal in
theorem padF_eq (msg : ByteArray) : padF msg = pad RATE msg := by
  have hk1 : 1 ≤ RATE - msg.size % RATE := by
    have := Nat.mod_lt msg.size (show 0 < RATE by decide); omega
  have hk2 : RATE - msg.size % RATE ≤ 136 := by simp only [RATE]; omega
  simp only [padF]
  rw [app_eq, copy_eq _ _ hk2]
  generalize hk : RATE - msg.size % RATE = k at hk1 hk2 ⊢
  have hpk : (padding RATE msg.size).data =
      ((Array.replicate k (0 : UInt8)).modify 0 (· ||| 0x01)).modify (k - 1) (· ||| 0x80) := by
    simp only [padding, hk]
  generalize hZ : msg ++ ({ data := Array.replicate k 0 } : ByteArray) = Z
  have hZs : Z.size = msg.size + k := by
    rw [← hZ, ByteArray.size_append]
    show msg.size + (Array.replicate k (0 : UInt8)).size = msg.size + k
    rw [Array.size_replicate]
  have hZi : ∀ i (h : i < Z.size), Z[i] = if h' : i < msg.size then msg[i] else 0 := by
    intro i h
    subst hZ
    split
    · rw [ByteArray.getElem_append_left]
    · rw [ByteArray.getElem_append_right (by omega), getElem_mk, Array.getElem_replicate]
  have hZn : Z.get! msg.size = 0 := by
    rw [get!_of_lt _ _ (by omega), hZi]; simp
  rw [hZn]
  generalize hY : Z.set! msg.size (0 ||| 1) = Y
  have hYs : Y.size = msg.size + k := by rw [← hY, ByteArray.size_set!, hZs]
  have hYi : ∀ i (h : i < Y.size), Y[i] = if msg.size = i then 1 else
      if h' : i < msg.size then msg[i] else 0 := by
    intro i h
    subst hY
    rw [ByteArray.getElem_set! _ _ _ _ (by omega) (by simpa using h)]
    split
    · rfl
    · rw [hZi]
  rw [hYs, get!_of_lt _ _ (by omega), hYi]
  have hpad : (padding RATE msg.size).size = k := by rw [size_padding', hk]
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_set!, hYs, pad, ByteArray.size_append, hpad]
  · intro i hi hi'
    rw [ByteArray.getElem_set! _ _ _ _ (by omega) (by simpa using hi)]
    simp only [pad] at hi' ⊢
    have hi2 : i < msg.size + k := by
      have := hi'; rw [ByteArray.size_append, hpad] at this; exact this
    by_cases hin : i < msg.size
    · rw [ByteArray.getElem_append_left hin]
      rw [ite_eq_right (by omega), hYi, ite_eq_right (by omega), dite_eq_left hin]
    · rw [ByteArray.getElem_append_right (by omega)]
      have hpi : (padding RATE msg.size)[i - msg.size]'(by rw [hpad]; omega) =
          (padding RATE msg.size).data[i - msg.size]'(by
            rw [hpk, Array.size_modify, Array.size_modify, Array.size_replicate]; omega) := rfl
      rw [hpi]
      simp only [hpk, Array.getElem_modify, Array.getElem_replicate]
      rw [hYi]
      by_cases h0 : msg.size = i
      · subst h0
        by_cases h1 : k = 1
        · subst h1; simp
        · rw [ite_eq_right (show ¬(msg.size + k - 1 = msg.size) by omega), ite_eq_left rfl,
            Nat.sub_self,
            ite_eq_right (show ¬(k - 1 = 0) by omega), ite_eq_left rfl]
          decide
      · rw [ite_eq_right h0, dite_eq_right hin]
        by_cases h1 : msg.size + k - 1 = i
        · subst h1
          have a1 : ¬ (msg.size = msg.size + k - 1) := by omega
          have a2 : ¬ (msg.size + k - 1 < msg.size) := by omega
          have a3 : msg.size + k - 1 - msg.size = k - 1 := by omega
          have a4 : ¬ (0 = k - 1) := by omega
          rw [ite_eq_left rfl, ite_eq_right a1, dite_eq_right a2, a3, ite_eq_left rfl, ite_eq_right
              a4]
        · rw [ite_eq_right h1, ite_eq_right (by omega), ite_eq_right (by omega)]


/-- Keccak-256 with the two-rounds-per-call permutation and in-place lane reads.

The bound `2^31 - 1` is a scalar `Nat` literal on a 32-bit target, so the test is one comparison.

`USize.size` itself is `2^32` there, a big number.

A message that long cannot be in memory on the M33.

On a 64-bit host the `else` branch is the spec, so the result is the same. -/
def keccak256U (msg : ByteArray) : Vector UInt8 DIGEST_LEN :=
  let padded := padF msg
  if hs : padded.size < 2147483647 then
    squeezeF (absorbU keccakF2 padded
      (Nat.lt_of_lt_of_le hs (Nat.le_trans (by decide) USize.le_size)) (blockCount RATE msg.size) 0
      (by show 0 + 136 * blockCount RATE msg.size ≤ (padF msg).size
          rw [Nat.zero_add, padF_eq, size_pad' (by decide)]; exact Nat.le_refl _) State.zero)
  else keccak256 msg


/-! ### `keccak256U = keccak256` -/

open EthLib.Base (byteAt) in
theorem uget_eq (bytes : ByteArray) (hs : bytes.size < USize.size) (p c : Nat)
    (h : p + c < bytes.size) (h' : (USize.ofNat p + USize.ofNat c).toNat < bytes.size) :
    bytes.uget (USize.ofNat p + USize.ofNat c) h' = byteAt bytes (p + c) := by
  have hp : p < 2 ^ System.Platform.numBits := by rw [← USize.size_eq_two_pow]; omega
  have hc : c < 2 ^ System.Platform.numBits := by rw [← USize.size_eq_two_pow]; omega
  have hpc : p + c < 2 ^ System.Platform.numBits := by rw [← USize.size_eq_two_pow]; omega
  have e : (USize.ofNat p + USize.ofNat c).toNat = p + c := by
    rw [USize.toNat_add, USize.toNat_ofNat', USize.toNat_ofNat', Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hpc]
  simp only [ByteArray.uget, byteAt, dite_eq_left h]
  show bytes.data[(USize.ofNat p + USize.ofNat c).toNat] = bytes.data[p + c]
  simp only [e]

open EthLib.Base (byteAt) in
theorem rdU_eq {bytes : ByteArray} (hs : bytes.size < USize.size) (p : Nat)
    (h : p + 136 ≤ bytes.size) (c : Nat) (hc : c < 136) :
    rdU bytes p h (USize.ofNat p) rfl c hc = (byteAt bytes (p + c)).toUInt64 := by
  simp only [rdU]
  rw [uget_eq bytes hs p c (by omega)]

theorem laneU_eq {bytes : ByteArray} (hs : bytes.size < USize.size) (p : Nat)
    (h : p + 136 ≤ bytes.size) (c : Nat) (hc : c + 8 ≤ 136) :
    laneU bytes hs p h (USize.ofNat p) rfl c hc = Internal.laneAt bytes (p + c) := by
  simp only [laneU, rdU_eq hs, Internal.laneAt, Nat.add_assoc]

theorem absorbU_eq (f : State → State) (bytes : ByteArray) (hs : bytes.size < USize.size) :
    ∀ (n p : Nat) (hp : p + 136 * n ≤ bytes.size) (S : State),
      absorbU f bytes hs n p hp S = Internal.absorbBlocks f RATE bytes n p S := by
  intro n
  induction n with
  | zero => intro p hp S; rfl
  | succ n ih =>
    intro p hp S
    simp only [absorbU, Internal.absorbBlocks]
    rw [ih]
    congr 2
    simp only [Internal.absorbBlock, Internal.blockLane, RATE, laneU_eq hs]
    simp

theorem squeezeF_eq (S : State) : squeezeF S = Internal.squeeze S := rfl

theorem keccak256U_eq : keccak256U = keccak256 := by
  funext msg
  simp only [keccak256U]
  split
  · rw [absorbU_eq, keccakF2_eq, squeezeF_eq, padF_eq]; rfl
  · rfl

/-- The proved in-place sponge.

It is not installed: `FastProofI.keccak256_eq_keccak256IG` is the `@[csimp]` for `keccak256`. -/
theorem keccak256_eq_keccak256U : keccak256 = keccak256U := keccak256U_eq.symm


/-! ### The other wrappers compiled inside `Keccak.lean`

`keccak512`, `Hasher.absorb` and `Hasher.digest` are compiled in the spec module.

The `keccakF` csimp is not in scope there, so their own code keeps the spec permutation.

Each copy below has the same body, compiled here after `keccakF_eq_keccakF2`.

So its `keccakF` becomes `keccakF2`.

The csimp lemmas, all `rfl`, send every later call to the copy. -/

/-- `keccak512`, recompiled with the fast permutation. -/
def keccak512R (msg : ByteArray) : Vector UInt8 DIGEST_LEN_512 :=
  Internal.squeeze512 (spongeAbsorb keccakF RATE_512 msg)

@[csimp] theorem keccak512_eq_keccak512R : keccak512 = keccak512R := rfl

/-- `Hasher.absorb`, recompiled with the fast permutation. -/
def hasherAbsorbR (h : Hasher) (data : ByteArray) : Hasher :=
  let bytes := h.pending ++ data
  let count := bytes.size / RATE
  ⟨Internal.absorbBlocks keccakF RATE bytes count 0 h.state,
    bytes.extract (RATE * count) bytes.size⟩

@[csimp] theorem hasherAbsorb_eq_R : @Hasher.absorb = @hasherAbsorbR := rfl

/-- `Hasher.digest`, recompiled with the fast permutation. -/
def hasherDigestR (h : Hasher) : Vector UInt8 DIGEST_LEN :=
  let last := h.pending ++ padding RATE h.pending.size
  Internal.squeeze (Internal.absorbBlocks keccakF RATE last 1 0 h.state)

@[csimp] theorem hasherDigest_eq_R : @Hasher.digest = @hasherDigestR := rfl

end EthLib.Cryptography.Hash.Keccak.Fast
