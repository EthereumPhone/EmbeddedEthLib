module

public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Ref

/-! Pad: the bytes and size of EthLib's padded message `pad m`. -/

public section

namespace EthLib.Cryptography.Hash.Sha256.ZsfProof
open EthLib.Cryptography.Hash.Sha256
open EthLib.Cryptography.Hash.Sha256.Zsf

private theorem size_mk (a : Array UInt8) : (ByteArray.mk a).size = a.size := rfl

private theorem lengthBytes_size (n : Nat) : (lengthBytes n).size = 8 := by
  simp [lengthBytes, size_mk]

theorem pad_size (m : ByteArray) : (pad m).size = m.size + 9 + paddingZeros m.size := by
  simp only [pad, ByteArray.size_append, lengthBytes_size, size_mk, Array.size_replicate,
    List.size_toArray, List.length_cons, List.length_nil]
  omega

theorem pad_size_mod (m : ByteArray) : (pad m).size % 64 = 0 := by
  rw [pad_size]; unfold paddingZeros; omega

/-- The message bytes come first. -/
theorem pad_getElem_lt (m : ByteArray) (i : Nat) (h : i < m.size) (h' : i < (pad m).size) :
    (pad m)[i] = m[i] := by
  simp only [pad]
  rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_append]; omega),
    ByteArray.getElem_append_left (by simp only [ByteArray.size_append]; omega),
    ByteArray.getElem_append_left h]

/-- Then the `0x80` byte. -/
theorem pad_getElem_size (m : ByteArray) (h' : m.size < (pad m).size) :
    (pad m)[m.size] = 0x80 := by
  simp only [pad]
  rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_append, size_mk]; simp; omega),
    ByteArray.getElem_append_left (by simp only [ByteArray.size_append, size_mk]; simp),
    ByteArray.getElem_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self]
  rfl

/-- Then `paddingZeros m.size` zero bytes. -/
theorem pad_getElem_zero (m : ByteArray) (i : Nat) (h1 : m.size < i)
    (h2 : i < m.size + 1 + paddingZeros m.size) (h' : i < (pad m).size) :
    (pad m)[i] = 0 := by
  simp only [pad]
  rw [ByteArray.getElem_append_left
      (by simp only [ByteArray.size_append, size_mk, Array.size_replicate]; simp; omega),
    ByteArray.getElem_append_right (by simp only [ByteArray.size_append, size_mk]; simp; omega)]
  simp only [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]

/-- Then the eight big-endian bytes of the bit length. -/
theorem pad_getElem_len (m : ByteArray) (j : Nat) (hj : j < 8)
    (h' : m.size + 1 + paddingZeros m.size + j < (pad m).size) :
    (pad m)[m.size + 1 + paddingZeros m.size + j] =
      ((UInt64.ofNat m.size * 8) >>> (56 - 8 * UInt64.ofNat j)).toUInt8 := by
  simp only [pad]
  rw [ByteArray.getElem_append_right
      (by simp only [ByteArray.size_append, size_mk, Array.size_replicate,
        List.size_toArray, List.length_cons, List.length_nil]; omega)]
  simp only [ByteArray.getElem_eq_getElem_data, lengthBytes, Array.getElem_ofFn]
  have hs : m.size + 1 + paddingZeros m.size + j -
      (m ++ ⟨#[0x80]⟩ ++ ⟨Array.replicate (paddingZeros m.size) 0⟩).size = j := by
    simp only [ByteArray.size_append, size_mk, Array.size_replicate,
      List.size_toArray, List.length_cons, List.length_nil]
    omega
  rw [hs]

end EthLib.Cryptography.Hash.Sha256.ZsfProof
