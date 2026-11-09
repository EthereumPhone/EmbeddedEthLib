module

public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Ref

/-! Digest: the eight in-place `put32` writes into any 32-byte buffer are EthLib's `digest`. -/

public section

namespace EthLib.Cryptography.Hash.Sha256.ZsfProof
open EthLib.Cryptography.Hash.Sha256
open EthLib.Cryptography.Hash.Sha256.Zsf


theorem digestInto_eq (out : ByteArray) (hout : out.size = 32) (S : State) :
    digestInto out hout S = digest S := by
  obtain ⟨⟨l⟩⟩ := out
  simp only [ByteArray.size, List.size_toArray] at hout
  match l, hout with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
     x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31], _ =>
    apply ByteArray.ext
    simp only [digestInto, put32, ByteArray.set, digest, byteAt, List.set_toArray,
      List.set_cons_succ, List.set_cons_zero, UInt32.shiftRight_zero]

end EthLib.Cryptography.Hash.Sha256.ZsfProof
