module

public import EthLib.Cryptography.Hash.Sha256.Spec
public import EthLib.Cryptography.Hash.Sha256.Zsf

/-!
# Reference definitions for the ZSf proof

Packaging only: every definition here is either a renaming of a piece of `EthLib.Cryptography.Hash.Sha256.Zsf.zloop` (its arguments grouped into EthLib's `State` and `Window`) or a fast-side window (the words ZSf loads into `w0..w15`). Nothing here is used by compiled code. The lemmas at the end are proved.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Sha256.ZsfProof
open EthLib.Cryptography.Hash.Sha256
open EthLib.Cryptography.Hash.Sha256.Zsf

/-- Fieldwise sum of two states: the feed-forward `H + (a..h)` that `zloop` computes at `t ≥ 64`. -/
def addS (H S : State) : State :=
  ⟨H.a + S.a, H.b + S.b, H.c + S.c, H.d + S.d, H.e + S.e, H.f + S.f, H.g + S.g, H.h + S.h⟩

/-- `n` schedule steps, the first step applied first (the order `rounds` applies them in). -/
def nextN : Nat → Window → Window
  | 0, w => w
  | n + 1, w => nextN n w.next

/-- The sixteen round constants `K[t] .. K[t+15]` (fewer if `t > 48`). -/
def kList (t : Nat) : List UInt32 := (K.toList.drop t).take 16

/-- `zloop` with its 8 + 8 + 16 word arguments grouped as `H : State`, `S : State`, `W : Window`. -/
def zloopS (fuel : Nat) (m : ByteArray) (out : ByteArray) (hout : out.size = 32) (ph : Ph) (s : Nat)
    (ho : s ≤ m.size) (t : UInt32) (H S : State) (W : Window) : ByteArray :=
  zloop fuel m out hout ph s ho t H.a H.b H.c H.d H.e H.f H.g H.h S.a S.b S.c S.d S.e S.f S.g S.h
    W.w0 W.w1 W.w2 W.w3 W.w4 W.w5 W.w6 W.w7 W.w8 W.w9 W.w10 W.w11 W.w12 W.w13 W.w14 W.w15

/-- The eight `put32` writes of `zloop`'s `.done` branch, applied to the words of `S` (the same expression, with the same proof terms, as in `EthLib.Cryptography.Hash.Sha256.Zsf.zloop`). -/
def digestInto (out : ByteArray) (hout : out.size = 32) (S : State) : ByteArray :=
  put32 (put32 (put32 (put32 (put32 (put32 (put32 (put32 out
    0 S.a (by omega)) 4 S.b (by simp [size_put32]; omega))
    8 S.c (by simp [size_put32]; omega)) 12 S.d (by simp [size_put32]; omega))
    16 S.e (by simp [size_put32]; omega)) 20 S.f (by simp [size_put32]; omega))
    24 S.g (by simp [size_put32]; omega)) 28 S.h (by simp [size_put32]; omega)

/-- High word of the 64-bit message length in bits (`zloop`'s `(bits >>> 32).toUInt32`). -/
def lenHi (m : ByteArray) : UInt32 := ((UInt64.ofNat m.size * 8) >>> 32).toUInt32

/-- Low word of the 64-bit message length in bits (`zloop`'s `bits.toUInt32`). -/
def lenLo (m : ByteArray) : UInt32 := (UInt64.ofNat m.size * 8).toUInt32

/-- The sixteen words of a full message block at `s`, as `zloop` loads them (through `wordAt`). -/
def fullWin (m : ByteArray) (s : Nat) (h : s + 64 ≤ m.size) : Window :=
  ⟨wordAt m s 0 (by omega), wordAt m s 1 (by omega), wordAt m s 2 (by omega),
    wordAt m s 3 (by omega), wordAt m s 4 (by omega), wordAt m s 5 (by omega),
    wordAt m s 6 (by omega), wordAt m s 7 (by omega), wordAt m s 8 (by omega),
    wordAt m s 9 (by omega), wordAt m s 10 (by omega), wordAt m s 11 (by omega),
    wordAt m s 12 (by omega), wordAt m s 13 (by omega), wordAt m s 14 (by omega),
    wordAt m s 15 (by omega)⟩

/-- The single last block (`r < 56`): fourteen tail words, then the length. -/
def tailWinShort (m : ByteArray) (s r : Nat) (hr : s + r = m.size) : Window :=
  ⟨tailWord m s r 0 hr, tailWord m s r 1 hr, tailWord m s r 2 hr, tailWord m s r 3 hr,
    tailWord m s r 4 hr, tailWord m s r 5 hr, tailWord m s r 6 hr, tailWord m s r 7 hr,
    tailWord m s r 8 hr, tailWord m s r 9 hr, tailWord m s r 10 hr, tailWord m s r 11 hr,
    tailWord m s r 12 hr, tailWord m s r 13 hr, lenHi m, lenLo m⟩

/-- The first of two last blocks (`56 ≤ r`): sixteen tail words. -/
def tailWinLong (m : ByteArray) (s r : Nat) (hr : s + r = m.size) : Window :=
  ⟨tailWord m s r 0 hr, tailWord m s r 1 hr, tailWord m s r 2 hr, tailWord m s r 3 hr,
    tailWord m s r 4 hr, tailWord m s r 5 hr, tailWord m s r 6 hr, tailWord m s r 7 hr,
    tailWord m s r 8 hr, tailWord m s r 9 hr, tailWord m s r 10 hr, tailWord m s r 11 hr,
    tailWord m s r 12 hr, tailWord m s r 13 hr, tailWord m s r 14 hr, tailWord m s r 15 hr⟩

/-- The second of two last blocks (`56 ≤ r`): zeros, then the length. -/
def lenWin (m : ByteArray) : Window :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, lenHi m, lenLo m⟩

/-! ## Proved structural facts -/

theorem nextN_zero (w : Window) : nextN 0 w = w := rfl

theorem nextN_succ (n : Nat) (w : Window) : nextN (n + 1) w = nextN n w.next := rfl

theorem nextN_add (n k : Nat) (w : Window) : nextN (n + k) w = nextN k (nextN n w) := by
  induction n generalizing w with
  | zero => simp [nextN]
  | succ n ih => rw [Nat.add_right_comm, nextN_succ, nextN_succ, ih]

theorem rounds_append (l₁ l₂ : List UInt32) (w : Window) (s : State) :
    rounds (l₁ ++ l₂) w s = rounds l₂ (nextN l₁.length w) (rounds l₁ w s) := by
  induction l₁ generalizing w s with
  | nil => rfl
  | cons k rest ih => simp only [List.cons_append, rounds, ih, List.length_cons, nextN_succ]

theorem K_toList_split : K.toList = kList 0 ++ kList 16 ++ kList 32 ++ kList 48 := rfl

theorem kList_length (t : Nat) (h : t ≤ 48) : (kList t).length = 16 := by
  simp [kList]; omega

theorem compress_eq (S : State) (bytes : ByteArray) (start : Nat) (whole : start + 64 ≤
    bytes.size) :
    compress S bytes start whole =
      addS S (rounds K.toList (Window.ofBlock bytes start whole) S) := by
  rw [compress]; rfl

theorem chain_zero (bytes : ByteArray) (start : Nat) (whole : start + 64 * 0 ≤ bytes.size) (S :
    State) :
    chain compress bytes 0 start whole S = S := by
  rw [chain]

theorem chain_succ (bytes : ByteArray) (count start : Nat) (whole : start + 64 * (count + 1) ≤
    bytes.size)
    (S : State) :
    chain compress bytes (count + 1) start whole S =
      chain compress bytes count (start + 64) (by omega) (compress S bytes start (by omega)) := by
  rw [chain]

/-- `Window.ofBlock` reads exactly the words `fullWin` reads (definitionally). -/
theorem ofBlock_eq_fullWin (bytes : ByteArray) (start : Nat) (whole : start + 64 ≤ bytes.size) :
    Window.ofBlock bytes start whole = fullWin bytes start whole := rfl

theorem zloopS_zero (m out : ByteArray) (hout : out.size = 32) (ph : Ph) (s : Nat) (ho : s ≤ m.size)
    (t : UInt32) (H S : State) (W : Window) : zloopS 0 m out hout ph s ho t H S W = out := rfl

end EthLib.Cryptography.Hash.Sha256.ZsfProof
