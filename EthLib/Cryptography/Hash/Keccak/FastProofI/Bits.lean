module

public import EthLib.Cryptography.Hash.Keccak.FastProof

/-! Bit lemmas for the interleaved Keccak: interleave and deinterleave, rotations, round constants.

embedded/gen/keccak/gen_proofI.py generates this file. -/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak.Fast
open EthLib.Cryptography.Hash.Keccak

/-! ## Bits of the interleave and deinterleave maps -/

theorem xor_cancel_left (a b : Bool) : (a ^^ (a ^^ b)) = b := by cases a <;> cases b <;> rfl

set_option maxHeartbeats 4000000 in
theorem ilvE64_bit (v : UInt64) (j : Nat) (hj : j < 32) :
    (ilvE64 v).toBitVec.getLsbD j = v.toBitVec.getLsbD (2 * j) := by
  unfold ilvE64 ilvE shuf
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
      j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
      j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨
      j = 30 ∨ j = 31) with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    (simp; try (ac_nf; simp only [Bool.xor_comm, Bool.xor_left_comm, xor_cancel_left,
      Bool.xor_self, Bool.false_xor]))

set_option maxHeartbeats 4000000 in
theorem ilvO64_bit (v : UInt64) (j : Nat) (hj : j < 32) :
    (ilvO64 v).toBitVec.getLsbD j = v.toBitVec.getLsbD (2 * j + 1) := by
  unfold ilvO64 ilvO shuf
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
      j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
      j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨
      j = 30 ∨ j = 31) with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    (simp; try (ac_nf; simp only [Bool.xor_comm, Bool.xor_left_comm, xor_cancel_left,
      Bool.xor_self, Bool.false_xor]))

set_option maxHeartbeats 4000000 in
theorem dlvLo_bit (e o : UInt32) (j : Nat) (hj : j < 32) :
    (dlvLo e o).toBitVec.getLsbD j =
      if j % 2 = 0 then e.toBitVec.getLsbD (j / 2) else o.toBitVec.getLsbD (j / 2) := by
  unfold dlvLo unshuf
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
      j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
      j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨
      j = 30 ∨ j = 31) with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    (simp; try (ac_nf; simp only [Bool.xor_comm, Bool.xor_left_comm, xor_cancel_left,
      Bool.xor_self, Bool.false_xor]))

set_option maxHeartbeats 4000000 in
theorem dlvHi_bit (e o : UInt32) (j : Nat) (hj : j < 32) :
    (dlvHi e o).toBitVec.getLsbD j =
      if j % 2 = 0 then e.toBitVec.getLsbD (16 + j / 2) else o.toBitVec.getLsbD (16 + j / 2) := by
  unfold dlvHi unshuf
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
      j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
      j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨
      j = 30 ∨ j = 31) with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    (simp; try (ac_nf; simp only [Bool.xor_comm, Bool.xor_left_comm, xor_cancel_left,
      Bool.xor_self, Bool.false_xor]))

theorem ilvE64_xor (a b : UInt64) : ilvE64 (a ^^^ b) = ilvE64 a ^^^ ilvE64 b := by
  apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [UInt32.toBitVec_xor, BitVec.getLsbD_xor, ilvE64_bit _ _ hj, UInt64.toBitVec_xor]

theorem ilvO64_xor (a b : UInt64) : ilvO64 (a ^^^ b) = ilvO64 a ^^^ ilvO64 b := by
  apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [UInt32.toBitVec_xor, BitVec.getLsbD_xor, ilvO64_bit _ _ hj, UInt64.toBitVec_xor]

theorem ilvE64_andn (a b : UInt64) : ilvE64 (~~~a &&& b) = ~~~ilvE64 a &&& ilvE64 b := by
  apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_not, BitVec.getLsbD_and, BitVec.getLsbD_not,
    ilvE64_bit _ _ hj, UInt64.toBitVec_and, UInt64.toBitVec_not]
  simp [hj, show 2 * j < 64 by omega]

theorem ilvO64_andn (a b : UInt64) : ilvO64 (~~~a &&& b) = ~~~ilvO64 a &&& ilvO64 b := by
  apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_not, BitVec.getLsbD_and, BitVec.getLsbD_not,
    ilvO64_bit _ _ hj, UInt64.toBitVec_and, UInt64.toBitVec_not]
  simp [hj, show 2 * j + 1 < 64 by omega]

theorem dlv64_bit (e o : UInt32) (k : Nat) (hk : k < 64) :
    (dlv64 e o).toBitVec.getLsbD k =
      if k % 2 = 0 then e.toBitVec.getLsbD (k / 2) else o.toBitVec.getLsbD (k / 2) := by
  have h32 : (UInt64.toBitVec 32 % 64) = 32#64 := by decide
  simp only [dlv64, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, BitVec.getLsbD_or,
    UInt32.toBitVec_toUInt64, h32, BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  by_cases hk32 : k < 32
  · have : ¬ (32 ≤ k) := by omega
    simp only [dlvLo_bit _ _ _ hk32, hk32, hk, decide_true, Bool.true_and,
      Bool.not_true, Bool.false_and, Bool.or_false, BitVec.toNat_ofNat]
  · have h2 : k - 32 < 32 := by omega
    have e1 : (k - 32) % 2 = k % 2 := by omega
    have e2 : 16 + (k - 32) / 2 = k / 2 := by omega
    rw [BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ k)]
    simp only [dlvHi_bit _ _ _ h2, e1, e2, hk, BitVec.toNat_ofNat]
    simp [hk32, show k - 32 < 64 by omega]

theorem dlv64_ilv (v : UInt64) : dlv64 (ilvE64 v) (ilvO64 v) = v := by
  apply UInt64.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [dlv64_bit _ _ _ hk]
  split
  · rw [ilvE64_bit _ _ (by omega)]; congr 1; omega
  · rw [ilvO64_bit _ _ (by omega)]; congr 1; omega

/-! ## Rotations -/

theorem rotl_bit (a : UInt64) (n : Nat) (hn : n < 64) (k : Nat) (hk : k < 64) :
    (rotl a (UInt64.ofNat n)).toBitVec.getLsbD k = a.toBitVec.getLsbD ((k + 64 - n) % 64) := by
  have h1 : (UInt64.ofNat n).toBitVec.toNat = n := by
    simp [UInt64.toBitVec_ofNat']; omega
  have h64 : BitVec.toNat (64 : BitVec 64) = 64 := rfl
  have h64' : (UInt64.toBitVec 64).toNat = 64 := rfl
  simp only [rotl, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_sub, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.toNat_umod, BitVec.toNat_sub, h1,
    h64, h64', Nat.mod_eq_of_lt hn, decide_eq_true hk, Bool.true_and]
  by_cases hkn : k < n
  · have e : (2 ^ 64 - n + 64) % 2 ^ 64 % 64 + k = (k + 64 - n) % 64 := by omega
    rw [e]; simp [hkn]
  · by_cases h0 : n = 0
    · subst h0; simp [Nat.mod_eq_of_lt hk]
    · have e : k - n = (k + 64 - n) % 64 := by omega
      have e2 : 64 ≤ (2 ^ 64 - n + 64) % 2 ^ 64 % 64 + k := by omega
      rw [BitVec.getLsbD_of_ge _ _ e2, e]; simp [hkn]

theorem rol32_bit (x : UInt32) (m : Nat) (hm : m < 32) (j : Nat) (hj : j < 32) :
    (rol32 x (UInt32.ofNat m)).toBitVec.getLsbD j = x.toBitVec.getLsbD ((j + 32 - m) % 32) := by
  have h1 : (UInt32.ofNat m).toBitVec.toNat = m := by
    simp [UInt32.toBitVec_ofNat']; omega
  have h32 : BitVec.toNat (32 : BitVec 32) = 32 := rfl
  have h32' : (UInt32.toBitVec 32).toNat = 32 := rfl
  simp only [rol32, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    UInt32.toBitVec_sub, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.toNat_umod, BitVec.toNat_sub, h1,
    h32, h32', Nat.mod_eq_of_lt hm, decide_eq_true hj, Bool.true_and]
  by_cases hkn : j < m
  · have e : (2 ^ 32 - m + 32) % 2 ^ 32 % 32 + j = (j + 32 - m) % 32 := by omega
    rw [e]; simp [hkn]
  · by_cases h0 : m = 0
    · subst h0; simp [Nat.mod_eq_of_lt hj]
    · have e : j - m = (j + 32 - m) % 32 := by omega
      have e2 : 32 ≤ (2 ^ 32 - m + 32) % 2 ^ 32 % 32 + j := by omega
      rw [BitVec.getLsbD_of_ge _ _ e2, e]; simp [hkn]

theorem rol32_zero (x : UInt32) : rol32 x 0 = x := by
  apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [show (0 : UInt32) = UInt32.ofNat 0 from rfl, rol32_bit _ _ (by decide) _ hj]
  congr 1; omega

theorem ilvE64_rotl_even (a : UInt64) (m : Nat) (hm : m < 32) :
    ilvE64 (rotl a (UInt64.ofNat (2 * m))) = rol32 (ilvE64 a) (UInt32.ofNat m) := by
  apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [ilvE64_bit _ _ hj, rotl_bit _ _ (by omega) _ (by omega), rol32_bit _ _ hm _ hj,
    ilvE64_bit _ _ (Nat.mod_lt _ (by decide))]
  congr 1; omega

theorem ilvO64_rotl_even (a : UInt64) (m : Nat) (hm : m < 32) :
    ilvO64 (rotl a (UInt64.ofNat (2 * m))) = rol32 (ilvO64 a) (UInt32.ofNat m) := by
  apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [ilvO64_bit _ _ hj, rotl_bit _ _ (by omega) _ (by omega), rol32_bit _ _ hm _ hj,
    ilvO64_bit _ _ (Nat.mod_lt _ (by decide))]
  congr 1; omega

theorem ilvE64_rotl_odd (a : UInt64) (m : Nat) (hm : m + 1 < 32) :
    ilvE64 (rotl a (UInt64.ofNat (2 * m + 1))) = rol32 (ilvO64 a) (UInt32.ofNat (m + 1)) := by
  apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [ilvE64_bit _ _ hj, rotl_bit _ _ (by omega) _ (by omega), rol32_bit _ _ hm _ hj,
    ilvO64_bit _ _ (Nat.mod_lt _ (by decide))]
  congr 1; omega

theorem ilvO64_rotl_odd (a : UInt64) (m : Nat) (hm : m < 32) :
    ilvO64 (rotl a (UInt64.ofNat (2 * m + 1))) = rol32 (ilvE64 a) (UInt32.ofNat m) := by
  apply UInt32.toBitVec_inj.1; apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [ilvO64_bit _ _ hj, rotl_bit _ _ (by omega) _ (by omega), rol32_bit _ _ hm _ hj,
    ilvE64_bit _ _ (Nat.mod_lt _ (by decide))]
  congr 1; omega

theorem ilvE64_rotl_0 (a : UInt64) : ilvE64 (rotl a 0) = ilvE64 a := by
  rw [show (0 : UInt64) = UInt64.ofNat (2 * 0) from rfl, ilvE64_rotl_even a 0 (by decide)]
  exact rol32_zero _
theorem ilvO64_rotl_0 (a : UInt64) : ilvO64 (rotl a 0) = ilvO64 a := by
  rw [show (0 : UInt64) = UInt64.ofNat (2 * 0) from rfl, ilvO64_rotl_even a 0 (by decide)]
  exact rol32_zero _
theorem ilvE64_rotl_1 (a : UInt64) : ilvE64 (rotl a 1) = rol32 (ilvO64 a) 1 :=
  ilvE64_rotl_odd a 0 (by decide)
theorem ilvO64_rotl_1 (a : UInt64) : ilvO64 (rotl a 1) = ilvE64 a := by
  rw [show (1 : UInt64) = UInt64.ofNat (2 * 0 + 1) from rfl, ilvO64_rotl_odd a 0 (by decide)]
  exact rol32_zero _
theorem ilvE64_rotl_2 (a : UInt64) : ilvE64 (rotl a 2) = rol32 (ilvE64 a) 1 :=
  ilvE64_rotl_even a 1 (by decide)
theorem ilvO64_rotl_2 (a : UInt64) : ilvO64 (rotl a 2) = rol32 (ilvO64 a) 1 :=
  ilvO64_rotl_even a 1 (by decide)
theorem ilvE64_rotl_3 (a : UInt64) : ilvE64 (rotl a 3) = rol32 (ilvO64 a) 2 :=
  ilvE64_rotl_odd a 1 (by decide)
theorem ilvO64_rotl_3 (a : UInt64) : ilvO64 (rotl a 3) = rol32 (ilvE64 a) 1 :=
  ilvO64_rotl_odd a 1 (by decide)
theorem ilvE64_rotl_6 (a : UInt64) : ilvE64 (rotl a 6) = rol32 (ilvE64 a) 3 :=
  ilvE64_rotl_even a 3 (by decide)
theorem ilvO64_rotl_6 (a : UInt64) : ilvO64 (rotl a 6) = rol32 (ilvO64 a) 3 :=
  ilvO64_rotl_even a 3 (by decide)
theorem ilvE64_rotl_8 (a : UInt64) : ilvE64 (rotl a 8) = rol32 (ilvE64 a) 4 :=
  ilvE64_rotl_even a 4 (by decide)
theorem ilvO64_rotl_8 (a : UInt64) : ilvO64 (rotl a 8) = rol32 (ilvO64 a) 4 :=
  ilvO64_rotl_even a 4 (by decide)
theorem ilvE64_rotl_10 (a : UInt64) : ilvE64 (rotl a 10) = rol32 (ilvE64 a) 5 :=
  ilvE64_rotl_even a 5 (by decide)
theorem ilvO64_rotl_10 (a : UInt64) : ilvO64 (rotl a 10) = rol32 (ilvO64 a) 5 :=
  ilvO64_rotl_even a 5 (by decide)
theorem ilvE64_rotl_14 (a : UInt64) : ilvE64 (rotl a 14) = rol32 (ilvE64 a) 7 :=
  ilvE64_rotl_even a 7 (by decide)
theorem ilvO64_rotl_14 (a : UInt64) : ilvO64 (rotl a 14) = rol32 (ilvO64 a) 7 :=
  ilvO64_rotl_even a 7 (by decide)
theorem ilvE64_rotl_15 (a : UInt64) : ilvE64 (rotl a 15) = rol32 (ilvO64 a) 8 :=
  ilvE64_rotl_odd a 7 (by decide)
theorem ilvO64_rotl_15 (a : UInt64) : ilvO64 (rotl a 15) = rol32 (ilvE64 a) 7 :=
  ilvO64_rotl_odd a 7 (by decide)
theorem ilvE64_rotl_18 (a : UInt64) : ilvE64 (rotl a 18) = rol32 (ilvE64 a) 9 :=
  ilvE64_rotl_even a 9 (by decide)
theorem ilvO64_rotl_18 (a : UInt64) : ilvO64 (rotl a 18) = rol32 (ilvO64 a) 9 :=
  ilvO64_rotl_even a 9 (by decide)
theorem ilvE64_rotl_20 (a : UInt64) : ilvE64 (rotl a 20) = rol32 (ilvE64 a) 10 :=
  ilvE64_rotl_even a 10 (by decide)
theorem ilvO64_rotl_20 (a : UInt64) : ilvO64 (rotl a 20) = rol32 (ilvO64 a) 10 :=
  ilvO64_rotl_even a 10 (by decide)
theorem ilvE64_rotl_21 (a : UInt64) : ilvE64 (rotl a 21) = rol32 (ilvO64 a) 11 :=
  ilvE64_rotl_odd a 10 (by decide)
theorem ilvO64_rotl_21 (a : UInt64) : ilvO64 (rotl a 21) = rol32 (ilvE64 a) 10 :=
  ilvO64_rotl_odd a 10 (by decide)
theorem ilvE64_rotl_25 (a : UInt64) : ilvE64 (rotl a 25) = rol32 (ilvO64 a) 13 :=
  ilvE64_rotl_odd a 12 (by decide)
theorem ilvO64_rotl_25 (a : UInt64) : ilvO64 (rotl a 25) = rol32 (ilvE64 a) 12 :=
  ilvO64_rotl_odd a 12 (by decide)
theorem ilvE64_rotl_27 (a : UInt64) : ilvE64 (rotl a 27) = rol32 (ilvO64 a) 14 :=
  ilvE64_rotl_odd a 13 (by decide)
theorem ilvO64_rotl_27 (a : UInt64) : ilvO64 (rotl a 27) = rol32 (ilvE64 a) 13 :=
  ilvO64_rotl_odd a 13 (by decide)
theorem ilvE64_rotl_28 (a : UInt64) : ilvE64 (rotl a 28) = rol32 (ilvE64 a) 14 :=
  ilvE64_rotl_even a 14 (by decide)
theorem ilvO64_rotl_28 (a : UInt64) : ilvO64 (rotl a 28) = rol32 (ilvO64 a) 14 :=
  ilvO64_rotl_even a 14 (by decide)
theorem ilvE64_rotl_36 (a : UInt64) : ilvE64 (rotl a 36) = rol32 (ilvE64 a) 18 :=
  ilvE64_rotl_even a 18 (by decide)
theorem ilvO64_rotl_36 (a : UInt64) : ilvO64 (rotl a 36) = rol32 (ilvO64 a) 18 :=
  ilvO64_rotl_even a 18 (by decide)
theorem ilvE64_rotl_39 (a : UInt64) : ilvE64 (rotl a 39) = rol32 (ilvO64 a) 20 :=
  ilvE64_rotl_odd a 19 (by decide)
theorem ilvO64_rotl_39 (a : UInt64) : ilvO64 (rotl a 39) = rol32 (ilvE64 a) 19 :=
  ilvO64_rotl_odd a 19 (by decide)
theorem ilvE64_rotl_41 (a : UInt64) : ilvE64 (rotl a 41) = rol32 (ilvO64 a) 21 :=
  ilvE64_rotl_odd a 20 (by decide)
theorem ilvO64_rotl_41 (a : UInt64) : ilvO64 (rotl a 41) = rol32 (ilvE64 a) 20 :=
  ilvO64_rotl_odd a 20 (by decide)
theorem ilvE64_rotl_43 (a : UInt64) : ilvE64 (rotl a 43) = rol32 (ilvO64 a) 22 :=
  ilvE64_rotl_odd a 21 (by decide)
theorem ilvO64_rotl_43 (a : UInt64) : ilvO64 (rotl a 43) = rol32 (ilvE64 a) 21 :=
  ilvO64_rotl_odd a 21 (by decide)
theorem ilvE64_rotl_44 (a : UInt64) : ilvE64 (rotl a 44) = rol32 (ilvE64 a) 22 :=
  ilvE64_rotl_even a 22 (by decide)
theorem ilvO64_rotl_44 (a : UInt64) : ilvO64 (rotl a 44) = rol32 (ilvO64 a) 22 :=
  ilvO64_rotl_even a 22 (by decide)
theorem ilvE64_rotl_45 (a : UInt64) : ilvE64 (rotl a 45) = rol32 (ilvO64 a) 23 :=
  ilvE64_rotl_odd a 22 (by decide)
theorem ilvO64_rotl_45 (a : UInt64) : ilvO64 (rotl a 45) = rol32 (ilvE64 a) 22 :=
  ilvO64_rotl_odd a 22 (by decide)
theorem ilvE64_rotl_55 (a : UInt64) : ilvE64 (rotl a 55) = rol32 (ilvO64 a) 28 :=
  ilvE64_rotl_odd a 27 (by decide)
theorem ilvO64_rotl_55 (a : UInt64) : ilvO64 (rotl a 55) = rol32 (ilvE64 a) 27 :=
  ilvO64_rotl_odd a 27 (by decide)
theorem ilvE64_rotl_56 (a : UInt64) : ilvE64 (rotl a 56) = rol32 (ilvE64 a) 28 :=
  ilvE64_rotl_even a 28 (by decide)
theorem ilvO64_rotl_56 (a : UInt64) : ilvO64 (rotl a 56) = rol32 (ilvO64 a) 28 :=
  ilvO64_rotl_even a 28 (by decide)
theorem ilvE64_rotl_61 (a : UInt64) : ilvE64 (rotl a 61) = rol32 (ilvO64 a) 31 :=
  ilvE64_rotl_odd a 30 (by decide)
theorem ilvO64_rotl_61 (a : UInt64) : ilvO64 (rotl a 61) = rol32 (ilvE64 a) 30 :=
  ilvO64_rotl_odd a 30 (by decide)
theorem ilvE64_rotl_62 (a : UInt64) : ilvE64 (rotl a 62) = rol32 (ilvE64 a) 31 :=
  ilvE64_rotl_even a 31 (by decide)
theorem ilvO64_rotl_62 (a : UInt64) : ilvO64 (rotl a 62) = rol32 (ilvO64 a) 31 :=
  ilvO64_rotl_even a 31 (by decide)

/-! ## Round constants -/

theorem rcE_all : ∀ k : Fin 24, ilvE64 (rcAt (UInt32.ofNat k.val)) = rcE (UInt32.ofNat k.val) := by
  decide

theorem rcO_all : ∀ k : Fin 24, ilvO64 (rcAt (UInt32.ofNat k.val)) = rcO (UInt32.ofNat k.val) := by
  decide

theorem rcE_eq (i : UInt32) (h : i.toNat < 24) : ilvE64 (rcAt i) = rcE i := by
  have := rcE_all ⟨i.toNat, h⟩
  simpa only [UInt32.ofNat_toNat] using this

theorem rcO_eq (i : UInt32) (h : i.toNat < 24) : ilvO64 (rcAt i) = rcO i := by
  have := rcO_all ⟨i.toNat, h⟩
  simpa only [UInt32.ofNat_toNat] using this


end EthLib.Cryptography.Hash.Keccak.Fast
