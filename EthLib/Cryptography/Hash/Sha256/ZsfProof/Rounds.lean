module

public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Ref

/-! Rounds: one sixteen-round chunk of `zloop` is sixteen EthLib rounds plus sixteen `Window.next`
    steps (none at `t = 48`); four chunks are `rounds K.toList`. -/

public section

namespace EthLib.Cryptography.Hash.Sha256.ZsfProof
open EthLib.Cryptography.Hash.Sha256
open EthLib.Cryptography.Hash.Sha256.Zsf

/-- One EthLib round and one schedule step, with the new words named. -/
private theorem rounds_step (k : UInt32) (rest : List UInt32)
    (a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 a' e' x : UInt32)
    (ha : a' = (h + EthLib.Cryptography.Hash.Sha256.Zsf.bigSigma1 e + EthLib.Cryptography.Hash.Sha256.Zsf.ch e f g + k + w0) + (EthLib.Cryptography.Hash.Sha256.Zsf.bigSigma0 a + EthLib.Cryptography.Hash.Sha256.Zsf.maj a b c))
    (he : e' = d + (h + EthLib.Cryptography.Hash.Sha256.Zsf.bigSigma1 e + EthLib.Cryptography.Hash.Sha256.Zsf.ch e f g + k + w0))
    (hx : x = w0 + EthLib.Cryptography.Hash.Sha256.Zsf.smallSigma0 w1 + w9 + EthLib.Cryptography.Hash.Sha256.Zsf.smallSigma1 w14) :
    rounds (k :: rest) ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ ⟨a, b, c, d, e, f, g, h⟩ =
      rounds rest ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, x⟩ ⟨a', a, b, c, e', e, f, g⟩ := by
  subst ha he hx
  rfl

private theorem chunk_lt (t t' : UInt32) (ht : t < 64) (h48 : t < 48) (htt : t + 16 = t')
    (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (ph : Ph) (s : Nat)
    (ho : s ≤ m.size) (H : State)
    (a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    zloopS (fuel + 1) m out hout ph s ho t H ⟨a, b, c, d, e, f, g, h⟩
        ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ =
      zloopS fuel m out hout ph s ho t' H
        (rounds [kAt (t + 0), kAt (t + 1), kAt (t + 2), kAt (t + 3), kAt (t + 4), kAt (t + 5),
          kAt (t + 6), kAt (t + 7), kAt (t + 8), kAt (t + 9), kAt (t + 10), kAt (t + 11),
          kAt (t + 12), kAt (t + 13), kAt (t + 14), kAt (t + 15)]
          ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ ⟨a, b, c, d, e, f, g, h⟩)
        (nextN 16 ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩) := by
  unfold zloopS
  rw [zloop.eq_2, dite_eq_left ht]
  extract_lets t1_0 t2_0 a0 e0 t1_1 t2_1 a1 e1 t1_2 t2_2 a2 e2 t1_3 t2_3 a3 e3 t1_4 t2_4 a4 e4 t1_5 t2_5 a5 e5 t1_6 t2_6 a6 e6 t1_7 t2_7 a7 e7 t1_8 t2_8 a8 e8 t1_9 t2_9 a9 e9 t1_10 t2_10 a10 e10 t1_11 t2_11 a11 e11 t1_12 t2_12 a12 e12 t1_13 t2_13 a13 e13 t1_14 t2_14 a14 e14 t1_15 t2_15 a15 e15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
  rw [ite_eq_left h48, htt]
  rw [rounds_step (kAt (t + 0)) _ a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 a0 e0 x0 rfl rfl rfl]
  rw [rounds_step (kAt (t + 1)) _ a0 a b c e0 e f g w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 x0 a1 e1 x1 rfl rfl rfl]
  rw [rounds_step (kAt (t + 2)) _ a1 a0 a b e1 e0 e f w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 x0 x1 a2 e2 x2 rfl rfl rfl]
  rw [rounds_step (kAt (t + 3)) _ a2 a1 a0 a e2 e1 e0 e w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 x0 x1 x2 a3 e3 x3 rfl rfl rfl]
  rw [rounds_step (kAt (t + 4)) _ a3 a2 a1 a0 e3 e2 e1 e0 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 x0 x1 x2 x3 a4 e4 x4 rfl rfl rfl]
  rw [rounds_step (kAt (t + 5)) _ a4 a3 a2 a1 e4 e3 e2 e1 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 x0 x1 x2 x3 x4 a5 e5 x5 rfl rfl rfl]
  rw [rounds_step (kAt (t + 6)) _ a5 a4 a3 a2 e5 e4 e3 e2 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 x0 x1 x2 x3 x4 x5 a6 e6 x6 rfl rfl rfl]
  rw [rounds_step (kAt (t + 7)) _ a6 a5 a4 a3 e6 e5 e4 e3 w7 w8 w9 w10 w11 w12 w13 w14 w15 x0 x1 x2 x3 x4 x5 x6 a7 e7 x7 rfl rfl rfl]
  rw [rounds_step (kAt (t + 8)) _ a7 a6 a5 a4 e7 e6 e5 e4 w8 w9 w10 w11 w12 w13 w14 w15 x0 x1 x2 x3 x4 x5 x6 x7 a8 e8 x8 rfl rfl rfl]
  rw [rounds_step (kAt (t + 9)) _ a8 a7 a6 a5 e8 e7 e6 e5 w9 w10 w11 w12 w13 w14 w15 x0 x1 x2 x3 x4 x5 x6 x7 x8 a9 e9 x9 rfl rfl rfl]
  rw [rounds_step (kAt (t + 10)) _ a9 a8 a7 a6 e9 e8 e7 e6 w10 w11 w12 w13 w14 w15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 a10 e10 x10 rfl rfl rfl]
  rw [rounds_step (kAt (t + 11)) _ a10 a9 a8 a7 e10 e9 e8 e7 w11 w12 w13 w14 w15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 a11 e11 x11 rfl rfl rfl]
  rw [rounds_step (kAt (t + 12)) _ a11 a10 a9 a8 e11 e10 e9 e8 w12 w13 w14 w15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 a12 e12 x12 rfl rfl rfl]
  rw [rounds_step (kAt (t + 13)) _ a12 a11 a10 a9 e12 e11 e10 e9 w13 w14 w15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 a13 e13 x13 rfl rfl rfl]
  rw [rounds_step (kAt (t + 14)) _ a13 a12 a11 a10 e13 e12 e11 e10 w14 w15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 a14 e14 x14 rfl rfl rfl]
  rw [rounds_step (kAt (t + 15)) _ a14 a13 a12 a11 e14 e13 e12 e11 w15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 a15 e15 x15 rfl rfl rfl]
  rfl

private theorem chunk_last (t t' : UInt32) (ht : t < 64) (h48 : ¬ t < 48) (htt : t + 16 = t')
    (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (ph : Ph) (s : Nat)
    (ho : s ≤ m.size) (H : State)
    (a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    zloopS (fuel + 1) m out hout ph s ho t H ⟨a, b, c, d, e, f, g, h⟩
        ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ =
      zloopS fuel m out hout ph s ho t' H
        (rounds [kAt (t + 0), kAt (t + 1), kAt (t + 2), kAt (t + 3), kAt (t + 4), kAt (t + 5),
          kAt (t + 6), kAt (t + 7), kAt (t + 8), kAt (t + 9), kAt (t + 10), kAt (t + 11),
          kAt (t + 12), kAt (t + 13), kAt (t + 14), kAt (t + 15)]
          ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ ⟨a, b, c, d, e, f, g, h⟩)
        ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := by
  unfold zloopS
  rw [zloop.eq_2, dite_eq_left ht]
  extract_lets t1_0 t2_0 a0 e0 t1_1 t2_1 a1 e1 t1_2 t2_2 a2 e2 t1_3 t2_3 a3 e3 t1_4 t2_4 a4 e4 t1_5 t2_5 a5 e5 t1_6 t2_6 a6 e6 t1_7 t2_7 a7 e7 t1_8 t2_8 a8 e8 t1_9 t2_9 a9 e9 t1_10 t2_10 a10 e10 t1_11 t2_11 a11 e11 t1_12 t2_12 a12 e12 t1_13 t2_13 a13 e13 t1_14 t2_14 a14 e14 t1_15 t2_15 a15 e15
  rw [ite_eq_right h48, htt]
  rw [rounds_step (kAt (t + 0)) _ a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 a0 e0 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 1)) _ a0 a b c e0 e f g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a1 e1 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 2)) _ a1 a0 a b e1 e0 e f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a2 e2 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 3)) _ a2 a1 a0 a e2 e1 e0 e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a3 e3 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 4)) _ a3 a2 a1 a0 e3 e2 e1 e0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a4 e4 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 5)) _ a4 a3 a2 a1 e4 e3 e2 e1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a5 e5 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 6)) _ a5 a4 a3 a2 e5 e4 e3 e2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a6 e6 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 7)) _ a6 a5 a4 a3 e6 e5 e4 e3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a7 e7 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 8)) _ a7 a6 a5 a4 e7 e6 e5 e4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a8 e8 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 9)) _ a8 a7 a6 a5 e8 e7 e6 e5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a9 e9 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 10)) _ a9 a8 a7 a6 e9 e8 e7 e6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a10 e10 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 11)) _ a10 a9 a8 a7 e10 e9 e8 e7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a11 e11 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 12)) _ a11 a10 a9 a8 e11 e10 e9 e8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a12 e12 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 13)) _ a12 a11 a10 a9 e12 e11 e10 e9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a13 e13 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 14)) _ a13 a12 a11 a10 e13 e12 e11 e10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a14 e14 _ rfl rfl rfl]
  rw [rounds_step (kAt (t + 15)) _ a14 a13 a12 a11 e14 e13 e12 e11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a15 e15 _ rfl rfl rfl]
  rfl

private theorem kList0 : kList 0 = [kAt (0 + 0), kAt (0 + 1), kAt (0 + 2), kAt (0 + 3), kAt (0 + 4), kAt (0 + 5), kAt (0 + 6), kAt (0 + 7), kAt (0 + 8), kAt (0 + 9), kAt (0 + 10), kAt (0 + 11), kAt (0 + 12), kAt (0 + 13), kAt (0 + 14), kAt (0 + 15)] := by decide

private theorem kList16 : kList 16 = [kAt (16 + 0), kAt (16 + 1), kAt (16 + 2), kAt (16 + 3), kAt (16 + 4), kAt (16 + 5), kAt (16 + 6), kAt (16 + 7), kAt (16 + 8), kAt (16 + 9), kAt (16 + 10), kAt (16 + 11), kAt (16 + 12), kAt (16 + 13), kAt (16 + 14), kAt (16 + 15)] := by decide

private theorem kList32 : kList 32 = [kAt (32 + 0), kAt (32 + 1), kAt (32 + 2), kAt (32 + 3), kAt (32 + 4), kAt (32 + 5), kAt (32 + 6), kAt (32 + 7), kAt (32 + 8), kAt (32 + 9), kAt (32 + 10), kAt (32 + 11), kAt (32 + 12), kAt (32 + 13), kAt (32 + 14), kAt (32 + 15)] := by decide

private theorem kList48 : kList 48 = [kAt (48 + 0), kAt (48 + 1), kAt (48 + 2), kAt (48 + 3), kAt (48 + 4), kAt (48 + 5), kAt (48 + 6), kAt (48 + 7), kAt (48 + 8), kAt (48 + 9), kAt (48 + 10), kAt (48 + 11), kAt (48 + 12), kAt (48 + 13), kAt (48 + 14), kAt (48 + 15)] := by decide


/-- Chunk `t = 0`: rounds `K[0..15]`, schedule moves on sixteen words. -/
theorem zloop_chunk0 (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (ph : Ph) (s : Nat)
    (ho : s ≤ m.size) (H S : State) (W : Window) :
    zloopS (fuel + 1) m out hout ph s ho 0 H S W =
      zloopS fuel m out hout ph s ho 16 H (rounds (kList 0) W S) (nextN 16 W) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := S
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := W
  rw [kList0]
  exact chunk_lt 0 16 (by decide) (by decide) (by decide) fuel m out hout ph s ho H a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

/-- Chunk `t = 16`: rounds `K[16..31]`. -/
theorem zloop_chunk16 (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (ph : Ph) (s : Nat)
    (ho : s ≤ m.size) (H S : State) (W : Window) :
    zloopS (fuel + 1) m out hout ph s ho 16 H S W =
      zloopS fuel m out hout ph s ho 32 H (rounds (kList 16) W S) (nextN 16 W) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := S
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := W
  rw [kList16]
  exact chunk_lt 16 32 (by decide) (by decide) (by decide) fuel m out hout ph s ho H a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

/-- Chunk `t = 32`: rounds `K[32..47]`. -/
theorem zloop_chunk32 (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (ph : Ph) (s : Nat)
    (ho : s ≤ m.size) (H S : State) (W : Window) :
    zloopS (fuel + 1) m out hout ph s ho 32 H S W =
      zloopS fuel m out hout ph s ho 48 H (rounds (kList 32) W S) (nextN 16 W) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := S
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := W
  rw [kList32]
  exact chunk_lt 32 48 (by decide) (by decide) (by decide) fuel m out hout ph s ho H a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

/-- Chunk `t = 48`: rounds `K[48..63]`; `zloop` passes the window on unchanged. -/
theorem zloop_chunk48 (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (ph : Ph) (s : Nat)
    (ho : s ≤ m.size) (H S : State) (W : Window) :
    zloopS (fuel + 1) m out hout ph s ho 48 H S W =
      zloopS fuel m out hout ph s ho 64 H (rounds (kList 48) W S) W := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := S
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := W
  rw [kList48]
  exact chunk_last 48 64 (by decide) (by decide) (by decide) fuel m out hout ph s ho H a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

/-- A whole block: four chunks are `rounds K.toList` (follows from the four chunks,
    `rounds_append`, `K_toList_split`, `kList_length`). -/
theorem zloop_block (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (ph : Ph) (s : Nat)
    (ho : s ≤ m.size) (H S : State) (W : Window) :
    zloopS (fuel + 4) m out hout ph s ho 0 H S W =
      zloopS fuel m out hout ph s ho 64 H (rounds K.toList W S) (nextN 48 W) := by
  rw [show fuel + 4 = fuel + 3 + 1 from rfl, zloop_chunk0, zloop_chunk16, zloop_chunk32, zloop_chunk48]
  have e1 : nextN 32 W = nextN 16 (nextN 16 W) := nextN_add 16 16 W
  have e2 : nextN 48 W = nextN 16 (nextN 16 (nextN 16 W)) := by rw [← e1]; exact nextN_add 32 16 W
  have l1 : (kList 0).length = 16 := kList_length 0 (by decide)
  have l2 : (kList 0 ++ kList 16).length = 32 := by
    rw [List.length_append, l1, kList_length 16 (by decide)]
  have l3 : (kList 0 ++ kList 16 ++ kList 32).length = 48 := by
    rw [List.length_append, l2, kList_length 32 (by decide)]
  rw [K_toList_split, rounds_append, rounds_append, rounds_append, l3, l2, l1, e2, e1]

end EthLib.Cryptography.Hash.Sha256.ZsfProof
