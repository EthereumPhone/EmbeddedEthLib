module

public import EthLib.Cryptography.Sphincs.TweakableHash

/-!
# A fast tweakable-hash wrapper for leanSPHINCS, proved equal to the spec

The spec builds each address with six `toByte` calls (`natToBytes`: a `List` of bytes per word, one cons cell per byte, Nat divisions), five `Vector` appends, and truncates the hash output with `Vector.ofFn` through a closure. Here every such function has a fast twin proved equal to it, and a `@[csimp]` lemma installs the twin in all code compiled after this module is imported.

- `encodeAdrs = encodeAdrsFast`: the 32 address bytes from shifts of the machine words, one array.
- `trunc = truncFast`: one `Array.extract` into an array of exactly `r` elements.
- `th = thFast`, `prf = prfR`: copies compiled after the two lemmas above, so they use them.
- `adrs`, `keyAdrs` and the eight address builders of `Address.lean`: copies compiled after `encodeAdrs = encodeAdrsFast`, because the originals are compiled inside `Address.lean`.

A csimp lemma rewrites only code compiled after it is in scope, so `Sphincs/Ots.lean` imports this module: `chainStep`, the chains, the Merkle and FORS node hashes and everything above them are compiled with the fast forms. Every theorem here is an equality of the spec's own constants, so the proofs about the spec are untouched.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Fast

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

/-! ## Addresses -/

/-- `encodeAdrs`, written byte by byte from the machine words: one array of 32 bytes. -/
def encodeAdrsFast (layer : UInt32) (tree : UInt64) (type keyPair word2 word3 : UInt32) : Adrs :=
  ⟨#[(layer >>> 24).toUInt8, (layer >>> 16).toUInt8, (layer >>> 8).toUInt8, layer.toUInt8,
      0, 0, 0, 0,
      (tree >>> 56).toUInt8, (tree >>> 48).toUInt8, (tree >>> 40).toUInt8, (tree >>> 32).toUInt8,
      (tree >>> 24).toUInt8, (tree >>> 16).toUInt8, (tree >>> 8).toUInt8, tree.toUInt8,
      (type >>> 24).toUInt8, (type >>> 16).toUInt8, (type >>> 8).toUInt8, type.toUInt8,
      (keyPair >>> 24).toUInt8, (keyPair >>> 16).toUInt8, (keyPair >>> 8).toUInt8, keyPair.toUInt8,
      (word2 >>> 24).toUInt8, (word2 >>> 16).toUInt8, (word2 >>> 8).toUInt8, word2.toUInt8,
      (word3 >>> 24).toUInt8, (word3 >>> 16).toUInt8, (word3 >>> 8).toUInt8, word3.toUInt8], rfl⟩

theorem b8 (n : Nat) (w : UInt8) (h : w.toNat = n % 256) : UInt8.ofNat n = w := by
  apply UInt8.toNat_inj.mp; simp [h]

theorem toByte4 (w : UInt32) : toByte 4 w.toNat =
    #v[(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8] := by
  simp only [toByte, EthLib.Base.natToBytes, EthLib.Base.natToBytes.go]
  congr 2
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply b8 <;>
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow] <;>
        simp <;> omega

theorem toByte12 (t : UInt64) : toByte 12 t.toNat =
    #v[(0 : UInt8), 0, 0, 0, (t >>> 56).toUInt8, (t >>> 48).toUInt8, (t >>> 40).toUInt8, (t >>>
        32).toUInt8,
      (t >>> 24).toUInt8, (t >>> 16).toUInt8, (t >>> 8).toUInt8, t.toUInt8] := by
  have ht := t.toNat_lt
  simp only [toByte, EthLib.Base.natToBytes, EthLib.Base.natToBytes.go]
  congr 2
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply b8 <;>
    (try simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]) <;>
    simp <;> omega

theorem encodeAdrs_eq : encodeAdrs = encodeAdrsFast := by
  funext layer tree type keyPair word2 word3
  simp only [encodeAdrs, encodeAdrsFast, toByte4, toByte12]
  apply Vector.toArray_inj.mp
  simp only [Vector.toArray_append, List.append_toArray, List.cons_append, List.nil_append]

/-! ### The address builders of `Address.lean`

They are compiled inside `Address.lean`, before `encodeAdrs_eq` exists, so each gets a copy compiled here and a csimp lemma that sends every later call to the copy. -/

/-- `adrs`, compiled with `encodeAdrsFast`. -/
def adrsR (type : AdrsType) (layer : Layer) (tree keyPair word2 word3 : Nat) : Adrs :=
  encodeAdrsFast (UInt32.ofNat layer.toNat) (UInt64.ofNat tree) type.code (UInt32.ofNat keyPair)
    (UInt32.ofNat word2) (UInt32.ofNat word3)

@[csimp] theorem adrs_eq : adrs = adrsR := by
  funext type layer tree keyPair word2 word3
  simp only [adrs, adrsR, encodeAdrs_eq]

/-- `keyAdrs`, compiled with `adrsR`. -/
def keyAdrsR (type : AdrsType) (key : OtsKey) (word2 word3 : Nat) : Adrs :=
  adrsR type key.layer key.tree key.leaf word2 word3

@[csimp] theorem keyAdrs_eq : keyAdrs = keyAdrsR := by
  funext type key word2 word3
  simp only [keyAdrs, keyAdrsR, adrs_eq]

/-- `adrsChain`, compiled with `keyAdrsR`. -/
def adrsChainR (key : OtsKey) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) : Adrs :=
  keyAdrsR .wotsHash key i.val mu.val

@[csimp] theorem adrsChain_eq : adrsChain = adrsChainR := by
  funext key i mu; simp only [adrsChain, adrsChainR, keyAdrs_eq]

/-- `adrsPk`, compiled with `keyAdrsR`. -/
def adrsPkR (key : OtsKey) : Adrs := keyAdrsR .wotsPk key 0 0

@[csimp] theorem adrsPk_eq : adrsPk = adrsPkR := by
  funext key; simp only [adrsPk, adrsPkR, keyAdrs_eq]

/-- `adrsNode`, compiled with `adrsR`. -/
def adrsNodeR (layer : Layer) (tree z j : Nat) : Adrs := adrsR .tree layer tree 0 z j

@[csimp] theorem adrsNode_eq : adrsNode = adrsNodeR := by
  funext layer tree z j; simp only [adrsNode, adrsNodeR, adrs_eq]

/-- `adrsPrf`, compiled with `keyAdrsR`. -/
def adrsPrfR (key : OtsKey) (i : Fin V) : Adrs := keyAdrsR .wotsPrf key i.val 0

@[csimp] theorem adrsPrf_eq : adrsPrf = adrsPrfR := by
  funext key i; simp only [adrsPrf, adrsPrfR, keyAdrs_eq]

/-- `adrsEnc`, compiled with `keyAdrsR`. -/
def adrsEncR (key : OtsKey) : Adrs := keyAdrsR .wotsEnc key 0 0

@[csimp] theorem adrsEnc_eq : adrsEnc = adrsEncR := by
  funext key; simp only [adrsEnc, adrsEncR, keyAdrs_eq]

/-- `adrsFors`, compiled with `keyAdrsR`. -/
def adrsForsR (idx z j : Nat) : Adrs := keyAdrsR .forsTree (OtsKey.ofIndex .bottom idx) z j

@[csimp] theorem adrsFors_eq : adrsFors = adrsForsR := by
  funext idx z j; simp only [adrsFors, adrsForsR, keyAdrs_eq]

/-- `adrsRoots`, compiled with `keyAdrsR`. -/
def adrsRootsR (idx : Nat) : Adrs := keyAdrsR .forsRoots (OtsKey.ofIndex .bottom idx) 0 0

@[csimp] theorem adrsRoots_eq : adrsRoots = adrsRootsR := by
  funext idx; simp only [adrsRoots, adrsRootsR, keyAdrs_eq]

/-- `adrsFprf`, compiled with `keyAdrsR`. -/
def adrsFprfR (idx j : Nat) : Adrs := keyAdrsR .forsPrf (OtsKey.ofIndex .bottom idx) 0 j

@[csimp] theorem adrsFprf_eq : adrsFprf = adrsFprfR := by
  funext idx j; simp only [adrsFprf, adrsFprfR, keyAdrs_eq]

/-! ## Truncation -/

/-- `Trunc_r` by `Array.extract`: one copy of the first `r` elements into an array of capacity `r`, instead of building a new array through a closure.

`Array.shrink` would pop the tail in place, but the result would keep the hash output's capacity of 32 elements. A signature holds about 480 digests, so on a 32-bit target that costs about 31 KB of arena while the signature is alive. -/
def truncFast {k : Nat} (r : Nat) (x : Vector UInt8 k) (h : r ≤ k := by decide) : Vector UInt8 r :=
  ⟨x.toArray.extract 0 r, by simp only [Array.size_extract, Vector.size_toArray]; omega⟩

@[csimp] theorem trunc_eq : @trunc = @truncFast := by
  funext k r x h
  apply Vector.ext
  intro i hi
  simp only [trunc, truncFast, Vector.getElem_ofFn, Vector.getElem_mk, Array.getElem_extract,
    Vector.getElem_toArray, Nat.zero_add]

/-! ## The tweakable hash -/

/-- `th`, compiled after `trunc_eq`. -/
def thFast {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32)) (pkSeed : PkSeed)
    (adrs : Adrs) (payload : ByteArray) : m Digest := do
  return trunc N (← H (thInput pkSeed adrs payload))

@[csimp] theorem th_eq : @th = @thFast := rfl

/-- `prf`, compiled after `th_eq`; `SK.seed`'s bytes are packed once per source, not once per call. -/
def prfR {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32)) (pkSeed : PkSeed)
    (skSeed : Seed) : Prf m :=
  let sk := packBytes skSeed
  fun adrs => th H pkSeed adrs sk

@[csimp] theorem prf_eq : @prf = @prfR := rfl

end EthLib.Cryptography.Sphincs.Fast
