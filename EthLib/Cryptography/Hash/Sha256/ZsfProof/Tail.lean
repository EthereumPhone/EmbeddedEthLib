module

public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Pad

/-! Tail: the last one or two blocks of `pad m`, from a block boundary `s` with `r = m.size - s < 64`
    message bytes left, are the windows `zloop` builds from `tailWord` and the length words. -/

public section

namespace EthLib.Cryptography.Hash.Sha256.ZsfProof
open EthLib.Cryptography.Hash.Sha256
open EthLib.Cryptography.Hash.Sha256.Zsf


/-- The two length words are the last eight bytes of `lengthBytes`, big-endian
    (the only genuine bit-vector identity of the proof). -/
theorem big32_len_hi (x : UInt64) :
    EthLib.Cryptography.Hash.Sha256.big32 (x >>> 56).toUInt8 (x >>> 48).toUInt8 (x >>> 40).toUInt8 (x >>> 32).toUInt8 =
      (x >>> 32).toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq
  simp only [EthLib.Cryptography.Hash.Sha256.big32, UInt8.toBitVec_toUInt32, UInt64.toBitVec_toUInt8,
    UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_toUInt32,
    UInt64.toBitVec_ofNat, UInt32.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceMod,
    BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) by omega) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h, show i < 16 by omega, show i < 24 by omega]
  · simp [h2, show ¬ i < 8 by omega, show i - 8 < 8 by omega, show i < 24 by omega,
      show 40 + (i - 8) = 32 + i by omega]
  · simp [show ¬ i < 8 by omega, show ¬ i < 16 by omega, show i - 16 < 8 by omega, h2,
      show ¬ i - 8 < 8 by omega, show 48 + (i - 16) = 32 + i by omega]
  · simp [show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show i - 24 < 8 by omega,
      show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega, show 56 + (i - 24) = 32 + i by omega]

theorem big32_len_lo (x : UInt64) :
    EthLib.Cryptography.Hash.Sha256.big32 (x >>> 24).toUInt8 (x >>> 16).toUInt8 (x >>> 8).toUInt8 (x >>> 0).toUInt8 =
      x.toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq
  simp only [EthLib.Cryptography.Hash.Sha256.big32, UInt8.toBitVec_toUInt32, UInt64.toBitVec_toUInt8,
    UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_toUInt32,
    UInt64.toBitVec_ofNat, UInt32.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceMod,
    BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) by omega) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h, show i < 16 by omega, show i < 24 by omega]
  · simp [h2, show ¬ i < 8 by omega, show i - 8 < 8 by omega, show i < 24 by omega,
      show 8 + (i - 8) = i by omega]
  · simp [show ¬ i < 8 by omega, show ¬ i < 16 by omega, show i - 16 < 8 by omega, h2,
      show ¬ i - 8 < 8 by omega, show 16 + (i - 16) = i by omega]
  · simp [show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show i - 24 < 8 by omega,
      show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega, show 24 + (i - 24) = i by omega]

/-! ### Byte- and word-level helpers -/

private theorem pad_80_at (m : ByteArray) (i : Nat) (hi : i = m.size) (h : i < (pad m).size) :
    (pad m)[i] = 0x80 := by
  subst hi; exact pad_getElem_size m h

private theorem pad_len_at (m : ByteArray) (i k : Nat) (hk : k < 8)
    (hi : i = m.size + 1 + paddingZeros m.size + k) (sh : UInt64) (hsh : 56 - 8 * UInt64.ofNat k = sh)
    (h : i < (pad m).size) :
    (pad m)[i] = ((UInt64.ofNat m.size * 8) >>> sh).toUInt8 := by
  subst hi; subst hsh; exact pad_getElem_len m k hk h

/-- A word strictly inside the zero run of the padding. -/
private theorem zero_word (m : ByteArray) (t j : Nat) (h1 : m.size < t + 4 * j)
    (h2 : t + 4 * j + 3 < m.size + 1 + paddingZeros m.size) (h : t + 4 * j + 3 < (pad m).size) :
    wordAt (pad m) t j h = 0 := by
  unfold wordAt
  rw [pad_getElem_zero m (t + 4 * j) (by omega) (by omega),
    pad_getElem_zero m (t + 4 * j + 1) (by omega) (by omega),
    pad_getElem_zero m (t + 4 * j + 2) (by omega) (by omega),
    pad_getElem_zero m (t + 4 * j + 3) (by omega) (by omega)]
  decide

/-- The high length word: the first four of the eight length bytes. -/
private theorem len_hi_word (m : ByteArray) (t j : Nat) (ht : t + 4 * j = m.size + 1 + paddingZeros m.size)
    (h : t + 4 * j + 3 < (pad m).size) : wordAt (pad m) t j h = lenHi m := by
  unfold wordAt
  rw [pad_len_at m (t + 4 * j) 0 (by decide) (by omega) 56 (by decide),
    pad_len_at m (t + 4 * j + 1) 1 (by decide) (by omega) 48 (by decide),
    pad_len_at m (t + 4 * j + 2) 2 (by decide) (by omega) 40 (by decide),
    pad_len_at m (t + 4 * j + 3) 3 (by decide) (by omega) 32 (by decide)]
  exact big32_len_hi _

/-- The low length word: the last four of the eight length bytes. -/
private theorem len_lo_word (m : ByteArray) (t j : Nat)
    (ht : t + 4 * j = m.size + 1 + paddingZeros m.size + 4)
    (h : t + 4 * j + 3 < (pad m).size) : wordAt (pad m) t j h = lenLo m := by
  unfold wordAt
  rw [pad_len_at m (t + 4 * j) 4 (by decide) (by omega) 24 (by decide),
    pad_len_at m (t + 4 * j + 1) 5 (by decide) (by omega) 16 (by decide),
    pad_len_at m (t + 4 * j + 2) 6 (by decide) (by omega) 8 (by decide),
    pad_len_at m (t + 4 * j + 3) 7 (by decide) (by omega) 0 (by decide)]
  exact big32_len_lo _

/-- A word of the tail block before the length bytes is `tailWord`. -/
private theorem tail_word (m : ByteArray) (s r j : Nat) (hr : s + r = m.size)
    (hz : s + 4 * j + 3 < m.size + 1 + paddingZeros m.size) (h : s + 4 * j + 3 < (pad m).size) :
    wordAt (pad m) s j h = tailWord m s r j hr := by
  unfold tailWord
  split
  · unfold wordAt
    rw [pad_getElem_lt m (s + 4 * j) (by omega), pad_getElem_lt m (s + 4 * j + 1) (by omega),
      pad_getElem_lt m (s + 4 * j + 2) (by omega), pad_getElem_lt m (s + 4 * j + 3) (by omega)]
  · split
    · exact zero_word m s j (by omega) hz h
    · unfold partialWord wordAt
      split
      · rw [pad_80_at m (s + 4 * j) (by omega),
          pad_getElem_zero m (s + 4 * j + 1) (by omega) (by omega),
          pad_getElem_zero m (s + 4 * j + 2) (by omega) (by omega),
          pad_getElem_zero m (s + 4 * j + 3) (by omega) (by omega)]
        decide
      · split
        · rw [pad_getElem_lt m (s + 4 * j) (by omega), pad_80_at m (s + 4 * j + 1) (by omega),
            pad_getElem_zero m (s + 4 * j + 2) (by omega) (by omega),
            pad_getElem_zero m (s + 4 * j + 3) (by omega) (by omega)]
          simp only [EthLib.Cryptography.Hash.Sha256.Zsf.big32, show (0x80 : UInt8).toUInt32 <<< 16 = (0x800000 : UInt32) by decide,
            show (0 : UInt32) <<< 8 = (0 : UInt32) by decide,
            show (0 : UInt8).toUInt32 = (0 : UInt32) by decide, UInt32.or_zero]
        · split
          · rw [pad_getElem_lt m (s + 4 * j) (by omega), pad_getElem_lt m (s + 4 * j + 1) (by omega),
              pad_80_at m (s + 4 * j + 2) (by omega),
              pad_getElem_zero m (s + 4 * j + 3) (by omega) (by omega)]
            simp only [EthLib.Cryptography.Hash.Sha256.Zsf.big32, show (0x80 : UInt8).toUInt32 <<< 8 = (0x8000 : UInt32) by decide,
              show (0 : UInt8).toUInt32 = (0 : UInt32) by decide, UInt32.or_zero]
          · rw [pad_getElem_lt m (s + 4 * j) (by omega), pad_getElem_lt m (s + 4 * j + 1) (by omega),
              pad_getElem_lt m (s + 4 * j + 2) (by omega), pad_80_at m (s + 4 * j + 3) (by omega)]
            simp only [EthLib.Cryptography.Hash.Sha256.Zsf.big32, show (0x80 : UInt8).toUInt32 = (0x80 : UInt32) by decide]

/-- One last block when fewer than 56 bytes are left. -/
theorem pad_size_short (m : ByteArray) (s r : Nat) (hs : s % 64 = 0) (hr : s + r = m.size)
    (h56 : r < 56) : (pad m).size = s + 64 := by
  rw [pad_size]; unfold paddingZeros; omega

/-- Two last blocks when 56 to 63 bytes are left. -/
theorem pad_size_long (m : ByteArray) (s r : Nat) (hs : s % 64 = 0) (hr : s + r = m.size)
    (h56 : 56 ≤ r) (h64 : r < 64) : (pad m).size = s + 128 := by
  rw [pad_size]; unfold paddingZeros; omega

theorem ofBlock_pad_short (m : ByteArray) (s r : Nat) (hs : s % 64 = 0) (hr : s + r = m.size)
    (h56 : r < 56) (whole : s + 64 ≤ (pad m).size) :
    Window.ofBlock (pad m) s whole = tailWinShort m s r hr := by
  have hpz : paddingZeros m.size = 55 - r := by unfold paddingZeros; omega
  rw [ofBlock_eq_fullWin]
  unfold fullWin tailWinShort
  congr 1
  all_goals first
    | exact tail_word m s r _ hr (by omega) _
    | exact len_hi_word m s _ (by omega) _
    | exact len_lo_word m s _ (by omega) _

theorem ofBlock_pad_long (m : ByteArray) (s r : Nat) (hs : s % 64 = 0) (hr : s + r = m.size)
    (h56 : 56 ≤ r) (h64 : r < 64) (whole : s + 64 ≤ (pad m).size) :
    Window.ofBlock (pad m) s whole = tailWinLong m s r hr := by
  have hpz : paddingZeros m.size = 119 - r := by unfold paddingZeros; omega
  rw [ofBlock_eq_fullWin]
  unfold fullWin tailWinLong
  congr 1
  all_goals exact tail_word m s r _ hr (by omega) _

theorem ofBlock_pad_len (m : ByteArray) (s r : Nat) (hs : s % 64 = 0) (hr : s + r = m.size)
    (h56 : 56 ≤ r) (h64 : r < 64) (whole : s + 64 + 64 ≤ (pad m).size) :
    Window.ofBlock (pad m) (s + 64) whole = lenWin m := by
  have hpz : paddingZeros m.size = 119 - r := by unfold paddingZeros; omega
  rw [ofBlock_eq_fullWin]
  unfold fullWin lenWin
  congr 1
  all_goals first
    | exact zero_word m (s + 64) _ (by omega) (by omega) _
    | exact len_hi_word m (s + 64) _ (by omega) _
    | exact len_lo_word m (s + 64) _ (by omega) _

end EthLib.Cryptography.Hash.Sha256.ZsfProof
