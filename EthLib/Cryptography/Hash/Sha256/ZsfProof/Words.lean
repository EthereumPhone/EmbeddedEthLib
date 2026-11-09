module

public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Pad

/-! Words: the full-block loads of `zloop` (`wordU`, `wordAtN`) are `wordAt`.

A full message block of `m` is the same block of `pad m`. -/

public section

namespace EthLib.Cryptography.Hash.Sha256.ZsfProof
open EthLib.Cryptography.Hash.Sha256
open EthLib.Cryptography.Hash.Sha256.Zsf

/-- `uget` at a `USize` offset is `getElem` at its `Nat` value. -/
private theorem uget_eq_getElem (bytes : ByteArray) (o : USize) (i : Nat) (hi : o.toNat = i)
    (h : o.toNat < bytes.size) (h' : i < bytes.size) : bytes.uget o h = bytes[i]'h' := by
  subst hi; rfl

theorem wordAtN_eq (bytes : ByteArray) (s j : Nat) (h : s + 4 * j + 3 < bytes.size) :
    wordAtN bytes s j h = wordAt bytes s j h := by
  rfl

/-- A `USize` load at offset `o = s + 4j` is `wordAt bytes s j`. -/
theorem wordU_eq (bytes : ByteArray) (o : USize) (s j : Nat) (hos : o.toNat = s + 4 * j)
    (hb : o.toNat < 1073741888) (h : o.toNat + 3 < bytes.size) (h' : s + 4 * j + 3 < bytes.size) :
    wordU bytes o hb h = wordAt bytes s j h' := by
  have h1 : (o + 1).toNat = s + 4 * j + 1 := by
    rw [add_toNat o 1 (by simp; omega)]; simp; omega
  have h2 : (o + 2).toNat = s + 4 * j + 2 := by
    rw [add_toNat o 2 (by simp; omega)]; simp; omega
  have h3 : (o + 3).toNat = s + 4 * j + 3 := by
    rw [add_toNat o 3 (by simp; omega)]; simp; omega
  unfold wordU wordAt
  rw [uget_eq_getElem bytes o (s + 4 * j) hos _ (by omega),
    uget_eq_getElem bytes (o + 1) (s + 4 * j + 1) h1 _ (by omega),
    uget_eq_getElem bytes (o + 2) (s + 4 * j + 2) h2 _ (by omega),
    uget_eq_getElem bytes (o + 3) (s + 4 * j + 3) h3 _ (by omega)]

/-- A word wholly inside the message reads the same from `pad m`. -/
theorem wordAt_pad (m : ByteArray) (s j : Nat) (h : s + 4 * j + 3 < m.size)
    (h' : s + 4 * j + 3 < (pad m).size) :
    wordAt (pad m) s j h' = wordAt m s j h := by
  unfold wordAt
  rw [pad_getElem_lt m (s + 4 * j) (by omega) (by omega),
    pad_getElem_lt m (s + 4 * j + 1) (by omega) (by omega),
    pad_getElem_lt m (s + 4 * j + 2) (by omega) (by omega),
    pad_getElem_lt m (s + 4 * j + 3) (by omega) (by omega)]

/-- A full message block is the same block of the padded message. -/
theorem ofBlock_pad_full (m : ByteArray) (s : Nat) (hs : s + 64 ≤ m.size)
    (whole : s + 64 ≤ (pad m).size) :
    Window.ofBlock (pad m) s whole = fullWin m s hs := by
  rw [ofBlock_eq_fullWin]
  unfold fullWin
  rw [wordAt_pad m s 0 (by omega), wordAt_pad m s 1 (by omega), wordAt_pad m s 2 (by omega),
    wordAt_pad m s 3 (by omega), wordAt_pad m s 4 (by omega), wordAt_pad m s 5 (by omega),
    wordAt_pad m s 6 (by omega), wordAt_pad m s 7 (by omega), wordAt_pad m s 8 (by omega),
    wordAt_pad m s 9 (by omega), wordAt_pad m s 10 (by omega), wordAt_pad m s 11 (by omega),
    wordAt_pad m s 12 (by omega), wordAt_pad m s 13 (by omega), wordAt_pad m s 14 (by omega),
    wordAt_pad m s 15 (by omega)]

end EthLib.Cryptography.Hash.Sha256.ZsfProof
