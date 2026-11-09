import EthLib.Cryptography.Sphincs

/-! Cortex-M33 benchmark entry for EthLib's leanSPHINCS (not part of EthLib).

Every input enters through `pq_load`, a C function that copies from a `volatile` blob.

So neither Lean nor GCC can fold any hash at compile time.

`pq_mark k` brackets each measured piece.

The QEMU instruction counter splits the trace at each executed `pq_mark`.

Modes (from C, `pq_mode`): 0 verify and pieces, 1 sign, 2 key generation.

Modes 3 and 4 call `signFast` and `keyGenFast` directly.

Sign and key generation compare their output with the known answers.

In this fork `sign` compiles to `signFast`, through the `@[csimp]` of `Sphincs/FastEq.lean`. -/

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

@[extern "pq_mark"] opaque mark (k : UInt32) : BaseIO Unit
@[extern "pq_mode"] opaque mode (u : Unit) : BaseIO UInt32
@[extern "pq_load"] opaque load (off len : UInt32) : BaseIO ByteArray
@[extern "pq_report"] opaque report (tag v : UInt32) : BaseIO Unit
@[extern "pq_report_bytes"] opaque reportBytes (tag : UInt32) (b : @& ByteArray) : BaseIO Unit

def OFF_PK : UInt32 := 0
def OFF_MSG : UInt32 := 32
def OFF_SIG : UInt32 := 64
def OFF_SEED : UInt32 := 64 + 7740

def vec32? (b : ByteArray) : Option (Vector UInt8 32) :=
  if h : b.size = 32 then some ⟨b.data, h⟩ else none

def vec16 (b : ByteArray) : Vector UInt8 16 :=
  if h : b.size = 16 then ⟨b.data, h⟩ else Vector.replicate 16 0

def toBA {n : Nat} (v : Vector UInt8 n) : ByteArray := ⟨v.toArray⟩

def b2u (b : Bool) : UInt32 := if b then 1 else 0

/-- Verify and isolated pieces.

Tags 1 and 2: the valid and the mutated verify.

Tags 3 to 6: keccak256 of 64 B, one WOTS chain step, one FORS leaf, one Merkle node.

Tags 7 to 9: one WOTS public leaf (257 calls), T_v (1072 B), one encoding trial (68 B). -/
def runVerify : BaseIO Unit := do
  -- Segment 1->2: load + decode (the C copy of 7.8 KB is part of this segment).
  mark 1
  let pkB ← load OFF_PK 32
  let msgB ← load OFF_MSG 32
  let sigB ← load OFF_SIG 7740
  let some msg := vec32? msgB | report 99 1
  let .ok pk := decodePublicKey pkB | report 99 2
  let .ok sig := decodeSignature sigB | report 99 3
  mark 2
  -- Segment 2->3: verify, valid signature.
  let ok := verify pk msg sig
  report 1 (b2u ok)
  mark 3
  -- Negative control: flip the low bit of the last byte (the top layer's last sibling).
  --
  -- Every layer is walked, and only the final root comparison can reject.
  let sigM := sigB.set! 7739 (sigB.get! 7739 ^^^ 1)
  let .ok sigMd := decodeSignature sigM | report 99 4
  mark 4
  let okM := verify pk msg sigMd
  report 2 (b2u okM)
  mark 5
  -- One Keccak-256 of 64 bytes (sig[0:64]): one permutation, the size of a chain step.
  let in64 ← load OFF_SIG 64
  mark 6
  let h := EthLib.Cryptography.Hash.Keccak.keccak256 in64
  reportBytes 3 (toBA h)
  mark 7
  -- One WOTS chain step: Th(PK.seed, ADRS_chain, value), 64-byte input.
  let key := OtsKey.ofIndex .bottom 12345
  let v0 := sig.bottom.chainValues[0]
  mark 8
  let c ← pure (chainStep hashId pk.pkSeed key ⟨0, by decide⟩ ⟨0, by decide⟩ v0).run
  reportBytes 4 (toBA c)
  mark 9
  -- One FORS leaf from the seed: PRF (80 B) then F (64 B), two calls.
  let seedB ← load OFF_SEED 32
  let some seed := vec32? seedB | report 99 5
  let secrets : Prf Id := prf hashId pk.pkSeed seed
  mark 10
  let fl := (forsLeaves hashId pk.pkSeed secrets 777 ⟨3, by decide⟩ 5).run
  reportBytes 5 (toBA fl)
  mark 11
  -- One hypertree node hash (80-byte input).
  let nd := (nodeHash hashId pk.pkSeed .middle 7 1 3 v0 c).run
  reportBytes 6 (toBA nd)
  mark 12
  -- One WOTS+C public leaf: 64 PRF + 192 chain steps + T_v (1072 B) = 257 calls, 264 permutations.
  let lf := (otsPublicLeaf hashId pk.pkSeed secrets key).run
  reportBytes 7 (toBA lf)
  mark 13
  -- T_v alone: 1072-byte input, 8 permutations.
  let tv := (otsLeafHash hashId pk.pkSeed key sig.bottom.chainValues).run
  reportBytes 8 (toBA tv)
  mark 14
  -- One WOTS+C encoding trial (68-byte input) = one signer counter trial.
  let e := (encode hashId pk.pkSeed key v0 (UInt32.ofNat 5)).run
  report 9 (match e with | some _ => 1 | none => 0)
  mark 15

def runSign : BaseIO Unit := do
  let seedB ← load OFF_SEED 32
  let msgB ← load OFF_MSG 32
  let sigB ← load OFF_SIG 7740
  let some seed := vec32? seedB | report 99 6
  let some msg := vec32? msgB | report 99 7
  mark 1
  match sign ⟨seed⟩ msg with
  | .ok s =>
    -- Mark 3 splits the arena peak of signing from that of encoding (with -DPQ_SEGPEAK).
    mark 3
    let out := encodeSignature s
    mark 2
    report 10 (b2u (out == sigB))
  | .error _ => report 99 8

def runKeyGen : BaseIO Unit := do
  let seedB ← load OFF_SEED 32
  let pkB ← load OFF_PK 32
  let some seed := vec32? seedB | report 99 9
  mark 1
  let (_, pk) := keyGen seed
  let out := encodePublicKey pk
  mark 2
  report 11 (b2u (out == pkB))

def runSignFast : BaseIO Unit := do
  let seedB ← load OFF_SEED 32
  let msgB ← load OFF_MSG 32
  let sigB ← load OFF_SIG 7740
  let some seed := vec32? seedB | report 99 6
  let some msg := vec32? msgB | report 99 7
  mark 1
  match signFast ⟨seed⟩ msg with
  | .ok s =>
    let out := encodeSignature s
    mark 2
    report 12 (b2u (out == sigB))
  | .error _ => report 99 8

def runKeyGenFast : BaseIO Unit := do
  let seedB ← load OFF_SEED 32
  let pkB ← load OFF_PK 32
  let some seed := vec32? seedB | report 99 9
  mark 1
  let (_, pk) := keyGenFast seed
  let out := encodePublicKey pk
  mark 2
  report 13 (b2u (out == pkB))

@[export lean_fw_main]
def fwMain (_ : Unit) : BaseIO Unit := do
  match ← mode () with
  | 1 => runSign
  | 2 => runKeyGen
  | 3 => runSignFast
  | 4 => runKeyGenFast
  | _ => runVerify
