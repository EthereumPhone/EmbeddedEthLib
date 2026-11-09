module

public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Rounds
public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Digest
public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Tail
public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Step

/-! Loop: the simulation. From a block boundary `s` of `m`, with hash value `addS H S`, `zloop` with enough fuel is the digest of EthLib's chain over the remaining `count` blocks of `pad m`. -/

public section

namespace EthLib.Cryptography.Hash.Sha256.ZsfProof
open EthLib.Cryptography.Hash.Sha256
open EthLib.Cryptography.Hash.Sha256.Zsf


/-- The tail: fewer than 64 message bytes left (one or two padded blocks remain). -/
theorem zloop_tail (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (s : Nat)
    (ho : s ≤ m.size) (hf : m.size < s + 64) (count : Nat) (hc : s + 64 * count = (pad m).size)
    (hfuel : 11 ≤ fuel) (H S : State) (W : Window) (whole : s + 64 * count ≤ (pad m).size) :
    zloopS fuel m out hout .body s ho 64 H S W =
      digest (chain compress (pad m) count s whole (addS H S)) := by
  have hs : s % 64 = 0 := by have := pad_size_mod m; omega
  obtain ⟨r, hr⟩ : ∃ r, s + r = m.size := ⟨m.size - s, by omega⟩
  by_cases h56 : r < 56
  · have hp := pad_size_short m s r hs hr h56
    obtain rfl : count = 1 := by omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 + 4 + 1 := ⟨fuel - 6, by omega⟩
    rw [step_tail_short _ m out hout s r ho hr h56, zloop_block, step_done, digestInto_eq,
      chain_succ, chain_zero, compress_eq, ofBlock_pad_short m s r hs hr h56]
  · have h56' : 56 ≤ r := by omega
    have h64 : r < 64 := by omega
    have hp := pad_size_long m s r hs hr h56' h64
    obtain rfl : count = 2 := by omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 + 4 + 1 + 4 + 1 := ⟨fuel - 11, by omega⟩
    rw [step_tail_long _ m out hout s r ho hr h56' h64, zloop_block, step_last, zloop_block,
      step_done, digestInto_eq, chain_succ, chain_succ, chain_zero, compress_eq, compress_eq,
      ofBlock_pad_long m s r hs hr h56' h64, ofBlock_pad_len m s r hs hr h56' h64]

/-- The simulation, by induction on `count`. -/
theorem zloop_sim (fuel : Nat) (m out : ByteArray) (hout : out.size = 32) (s : Nat)
    (ho : s ≤ m.size) (count : Nat) (hc : s + 64 * count = (pad m).size)
    (hfuel : 5 * ((m.size - s) / 64) + 11 ≤ fuel) (H S : State) (W : Window)
    (whole : s + 64 * count ≤ (pad m).size) :
    zloopS fuel m out hout .body s ho 64 H S W =
      digest (chain compress (pad m) count s whole (addS H S)) := by
  induction count generalizing fuel s H S W with
  | zero =>
    have := pad_size m
    omega
  | succ k ih =>
    by_cases hf : s + 64 ≤ m.size
    · obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 + 1 := ⟨fuel - 5, by omega⟩
      rw [step_full _ m out hout s ho hf, zloop_block,
        ih f (s + 64) hf (by omega) (by omega) (addS H S) _ _ (by omega),
        chain_succ, compress_eq, ofBlock_pad_full m s hf]
    · exact zloop_tail fuel m out hout s ho (by omega) (k + 1) hc (by omega) H S W whole

end EthLib.Cryptography.Hash.Sha256.ZsfProof
