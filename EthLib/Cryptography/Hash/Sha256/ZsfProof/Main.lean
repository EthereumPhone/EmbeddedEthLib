module

public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Loop

/-! The whole hash, and the compiler substitutions. -/

public section

namespace EthLib.Cryptography.Hash.Sha256.ZsfProof
open EthLib.Cryptography.Hash
open EthLib.Cryptography.Hash.Sha256 (hash32)

/-- The initial state as `zloop` receives it (eight literals) plus the zero working state. -/
private theorem addS_init :
    addS ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
      0x5be0cd19⟩ ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ = Sha256.initial := by
  rfl

/-- The spec hash, with the padded buffer abstracted (avoids unfolding `pad` under `whnf`). -/
private theorem hash_via (m : ByteArray) (p : ByteArray) (hp : Sha256.pad m = p) (S : Sha256.State)
    (hS : S = Sha256.initial) (count : Nat) (hcount : count = p.size / 64)
    (whole : 0 + 64 * count ≤ p.size) :
    Sha256.digest (Sha256.chain Sha256.compress p count 0 whole S) = Sha256.hash m := by
  subst hp hS hcount
  rfl

theorem hashInto_eq (m out : ByteArray) : EthLib.Cryptography.Hash.Sha256.Zsf.hashInto m out =
    Sha256.hash m := by
  have hout : (if out.size = 32 then out else EthLib.Cryptography.Hash.Sha256.Zsf.zeros32).size =
      32 := by
    split
    · assumption
    · exact EthLib.Cryptography.Hash.Sha256.Zsf.zeros32_size
  have h1 : EthLib.Cryptography.Hash.Sha256.Zsf.hashInto m out =
      zloopS (5 * (m.size / 64) + 16) m (if out.size = 32 then out else
          EthLib.Cryptography.Hash.Sha256.Zsf.zeros32) hout
        .body 0 (Nat.zero_le _) 64
        ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
          0x5be0cd19⟩ ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
        ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
    unfold EthLib.Cryptography.Hash.Sha256.Zsf.hashInto
    rw [dite_eq_left hout]
    rfl
  have hmod := pad_size_mod m
  have hc : 0 + 64 * ((Sha256.pad m).size / 64) = (Sha256.pad m).size := by omega
  have hfuel : 5 * ((m.size - 0) / 64) + 11 ≤ 5 * (m.size / 64) + 16 := by
    rw [Nat.sub_zero]; omega
  rw [h1, zloop_sim (5 * (m.size / 64) + 16) m _ hout 0 (Nat.zero_le _) ((Sha256.pad m).size / 64)
      hc
    hfuel _ _ _ (Nat.le_of_eq hc), addS_init]
  exact hash_via m (Sha256.pad m) rfl _ rfl _ rfl _

theorem hashZ_eq (m : ByteArray) : EthLib.Cryptography.Hash.Sha256.Zsf.hashZ m = Sha256.hash m :=
    hashInto_eq m EthLib.Cryptography.Hash.Sha256.Zsf.zeros32

/-- Compiled code that calls `hash` runs `EthLib.Cryptography.Hash.Sha256.Zsf.hashZ`.

The kernel still reasons about `hash`. -/
@[csimp] theorem hash_eq_hashZ : @Sha256.hash = @EthLib.Cryptography.Hash.Sha256.Zsf.hashZ := by
  funext m
  exact (hashZ_eq m).symm

/-- `hash32` with the fast hash inside: the same 32 bytes as a `Vector`. -/
def hash32Z (message : ByteArray) : Vector UInt8 32 :=
  ⟨(EthLib.Cryptography.Hash.Sha256.Zsf.hashZ message).data,
    by rw [hashZ_eq]; exact (hash32 message).2⟩

/-- Two `Vector.mk`s over the data of equal byte arrays are equal, stated over free `a b`.

A `simp`/`Vector.ext`/`getElem` proof of `hash32_eq_hash32Z` passed the elaboration-time kernel.

It took milliseconds there, but did not finish under `leanchecker` replay in 600 s.

The cause was not isolated.

The term proof through this lemma replays in about 0 ms. -/
private theorem vector_mk_data_eq (a b : ByteArray) (h : a = b) (pa : a.data.size = 32)
    (pb : b.data.size = 32) : (⟨a.data, pa⟩ : Vector UInt8 32) = ⟨b.data, pb⟩ := by
  subst h
  rfl

/-- `hash32` was compiled before `hash_eq_hashZ` existed, so it gets its own substitution. -/
@[csimp] theorem hash32_eq_hash32Z : @hash32 = @hash32Z :=
  funext fun m => vector_mk_data_eq _ _ (hashZ_eq m).symm _ _

end EthLib.Cryptography.Hash.Sha256.ZsfProof

namespace EthLib.Cryptography.Hash

/-- The public `sha256` is `@[inline]`.

Its saved body calls `hash`, compiled before `hash_eq_hashZ` existed.

So it gets its own substitution. -/
@[csimp] theorem sha256_eq_hashZ : @sha256 = @EthLib.Cryptography.Hash.Sha256.Zsf.hashZ := by
  funext m
  exact (EthLib.Cryptography.Hash.Sha256.ZsfProof.hashZ_eq m).symm

end EthLib.Cryptography.Hash

namespace EthLib.Cryptography.Hash.Sha256.Zsf

/-- Public form of the correctness theorem, next to `Zsf.hashInto`.

Whatever buffer the caller passes, `hashInto` returns the SHA-256 digest of the message.

A caller that owns an exclusive 32-byte buffer gets the digest written into it without allocation.
-/
theorem hashInto_eq (m out : ByteArray) : hashInto m out = Sha256.hash m :=
  ZsfProof.hashInto_eq m out

/-- Public form of `hashZ = hash`. -/
theorem hashZ_eq (m : ByteArray) : hashZ m = Sha256.hash m :=
  ZsfProof.hashZ_eq m

end EthLib.Cryptography.Hash.Sha256.Zsf
