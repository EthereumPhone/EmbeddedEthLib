module

public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Words

/-! Step: one call of `zloop` at a block boundary (`t = 64`), in each phase. -/

public section

namespace EthLib.Cryptography.Hash.Sha256.ZsfProof
open EthLib.Cryptography.Hash.Sha256
open EthLib.Cryptography.Hash.Sha256.Zsf

private theorem uget_eq' (m : ByteArray) (o : USize) (h : o.toNat < m.size) :
    m.uget o h = m[o.toNat]'h := by
  cases m; rfl

private theorem getElem_congr' (m : ByteArray) {a b : Nat} (hab : a = b) (ha : a < m.size)
    (hb : b < m.size) : m[a] = m[b] := by
  subst hab; rfl

/-- A `USize` load at offset `o = s + 4j` is `wordAt bytes s j` (local copy of `wordU_eq`). -/
private theorem wordU_eq' (bytes : ByteArray) (o : USize) (s j : Nat) (hos : o.toNat = s + 4 * j)
    (hb : o.toNat < 1073741888) (h : o.toNat + 3 < bytes.size) (h' : s + 4 * j + 3 < bytes.size) :
    wordU bytes o hb h = wordAt bytes s j h' := by
  unfold wordU wordAt
  simp only [uget_eq']
  congr 1
  · exact getElem_congr' _ hos _ _
  · exact getElem_congr' _ (by rw [add_toNat o 1 (by simp; omega)]; simp; omega) _ _
  · exact getElem_congr' _ (by rw [add_toNat o 2 (by simp; omega)]; simp; omega) _ _
  · exact getElem_congr' _ (by rw [add_toNat o 3 (by simp; omega)]; simp; omega) _ _

private theorem wU_0 (m : ByteArray) (s : Nat) (hs : m.size < 1073741824) (hf : s + 64 ≤ m.size)
    (hb : s.toUInt32.toUSize.toNat < 1073741888) (h : s.toUInt32.toUSize.toNat + 3 < m.size) :
    wordU m s.toUInt32.toUSize hb h = wordAt m s 0 (by omega) :=
  wordU_eq' _ _ _ _ (by simp [UInt32.toNat_toUSize]; omega) _ _ _

private theorem wU_k (m : ByteArray) (s k : Nat) (c : USize) (hc : c.toNat = 4 * k)
    (hs : m.size < 1073741824) (hf : s + 64 ≤ m.size) (hk : k < 16)
    (hb : (s.toUInt32.toUSize + c).toNat < 1073741888)
    (h : (s.toUInt32.toUSize + c).toNat + 3 < m.size) :
    wordU m (s.toUInt32.toUSize + c) hb h = wordAt m s k (by omega) := by
  have hoe : s.toUInt32.toUSize.toNat = s := by simp [UInt32.toNat_toUSize]; omega
  exact wordU_eq' _ _ _ _ (by rw [add_toNat _ _ (by omega), hoe, hc]) _ _ _


/-- `.done`: the digest is written into `out`. -/
theorem step_done (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (s : Nat) (ho : s ≤
    m.size)
    (H S : State) (W : Window) :
    zloopS (fuel + 1) m out hout .done s ho 64 H S W = digestInto out hout (addS H S) := by
  unfold zloopS
  rw [zloop.eq_def]
  simp only [show ¬ ((64 : UInt32) < 64) from by decide, dite_false]
  rfl

/-- `.last`: the zero-and-length block. -/
theorem step_last (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (s : Nat) (ho : s ≤
    m.size)
    (H S : State) (W : Window) :
    zloopS (fuel + 1) m out hout .last s ho 64 H S W =
      zloopS fuel m out hout .done s ho 0 (addS H S) (addS H S) (lenWin m) := by
  unfold zloopS
  rw [zloop.eq_def]
  simp only [show ¬ ((64 : UInt32) < 64) from by decide, dite_false]
  rfl

/-- `.body` with a full message block at `s` (either load path). -/
theorem step_full (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (s : Nat) (ho : s ≤
    m.size)
    (hf : s + 64 ≤ m.size) (H S : State) (W : Window) :
    zloopS (fuel + 1) m out hout .body s ho 64 H S W =
      zloopS fuel m out hout .body (s + 64) hf 0 (addS H S) (addS H S) (fullWin m s hf) := by
  unfold zloopS
  rw [zloop.eq_def]
  simp only [show ¬ ((64 : UInt32) < 64) from by decide, dite_false]
  rw [dite_eq_left hf]
  split
  · rename_i hs
    rw [wU_0 m s hs hf,
      wU_k m s 1 4 (by simp) hs hf (by decide),
      wU_k m s 2 8 (by simp) hs hf (by decide),
      wU_k m s 3 12 (by simp) hs hf (by decide),
      wU_k m s 4 16 (by simp) hs hf (by decide),
      wU_k m s 5 20 (by simp) hs hf (by decide),
      wU_k m s 6 24 (by simp) hs hf (by decide),
      wU_k m s 7 28 (by simp) hs hf (by decide),
      wU_k m s 8 32 (by simp) hs hf (by decide),
      wU_k m s 9 36 (by simp) hs hf (by decide),
      wU_k m s 10 40 (by simp) hs hf (by decide),
      wU_k m s 11 44 (by simp) hs hf (by decide),
      wU_k m s 12 48 (by simp) hs hf (by decide),
      wU_k m s 13 52 (by simp) hs hf (by decide),
      wU_k m s 14 56 (by simp) hs hf (by decide),
      wU_k m s 15 60 (by simp) hs hf (by decide)]
    rfl
  · rfl

/-- `.body` with `r < 56` bytes left: one last block, then `.done`. -/
theorem step_tail_short (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (s r : Nat)
    (ho : s ≤ m.size) (hr : s + r = m.size) (h56 : r < 56) (H S : State) (W : Window) :
    zloopS (fuel + 1) m out hout .body s ho 64 H S W =
      zloopS fuel m out hout .done s ho 0 (addS H S) (addS H S) (tailWinShort m s r hr) := by
  obtain rfl : r = m.size - s := by omega
  unfold zloopS
  rw [zloop.eq_def]
  simp only [show ¬ ((64 : UInt32) < 64) from by decide, dite_false]
  rw [dite_eq_right (by omega : ¬ (s + 64 ≤ m.size)), ite_eq_left h56]
  rfl

/-- `.body` with `56 ≤ r < 64` bytes left: the first of two last blocks, then `.last`. -/
theorem step_tail_long (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (s r : Nat)
    (ho : s ≤ m.size) (hr : s + r = m.size) (h56 : 56 ≤ r) (h64 : r < 64) (H S : State) (W :
        Window) :
    zloopS (fuel + 1) m out hout .body s ho 64 H S W =
      zloopS fuel m out hout .last s ho 0 (addS H S) (addS H S) (tailWinLong m s r hr) := by
  obtain rfl : r = m.size - s := by omega
  unfold zloopS
  rw [zloop.eq_def]
  simp only [show ¬ ((64 : UInt32) < 64) from by decide, dite_false]
  rw [dite_eq_right (by omega : ¬ (s + 64 ≤ m.size)), ite_eq_right (by omega : ¬ (m.size - s < 56))]
  rfl

end EthLib.Cryptography.Hash.Sha256.ZsfProof
