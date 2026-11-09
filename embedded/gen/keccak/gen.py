# Writes EthLib/Cryptography/Hash/Keccak/Fast.lean (Keccak-f[1600], padding, lane reads); gen_i.py appends to it.
# Run regen.py rather than this script alone.
import os
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from layout import pack
RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
RHO = [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14]
PI = [0,6,12,18,24,3,9,10,16,22,1,7,13,19,20,4,5,11,17,23,2,8,14,15,21]
L = range(25)
def rnd(i, o, s, rc, ind="  "):
    """lets computing output lanes {o}0..24 from input lanes {i}0..24; temporaries suffixed s."""
    out = []
    for x in range(5):
        out.append(f"{ind}let c{x}{s} := {i}{x} ^^^ {i}{x+5} ^^^ {i}{x+10} ^^^ {i}{x+15} ^^^ {i}{x+20}")
    for x in range(5):
        out.append(f"{ind}let d{x}{s} := c{(x+4)%5}{s} ^^^ rotl c{(x+1)%5}{s} 1")
    for k in L:
        out.append(f"{ind}let r{k}{s} := rotl ({i}{k} ^^^ d{k%5}{s}) {RHO[k]}")
    for y in range(5):
        for x in range(5):
            k = 5*y + x
            p = lambda xx: f"r{PI[5*y + xx % 5]}{s}"
            e = f"{p(x)} ^^^ (~~~{p(x+1)} &&& {p(x+2)})"
            if k == 0: e = f"({e}) ^^^ {rc}"
            out.append(f"{ind}let {o}{k} := {e}")
    return out
lines = []
w = lines.append
w("""module

public import EthLib.Cryptography.Hash.Keccak.Spec

/-!
# Keccak, fast form

The functions here compute `keccakF` and `keccak256` of `EthLib.Cryptography.Hash.Keccak`.

They are written so that a 32-bit target keeps all 25 lanes of the state unboxed.

The lanes are `UInt64` parameters and locals, and each round is straight-line code.

Every rotation is by a literal amount, and `rcAt` gives the round constants as match arms.

The bit-interleaved form keeps each lane as two `UInt32` halves, its even and its odd bits.

`embedded/gen/keccak/gen.py` and `gen_i.py` generate this file, and `regen.py` runs them.

`Keccak/FastProof.lean` proves `keccakF1 = keccakF` and `keccakF2 = keccakF`.

It installs `keccakF2` with `@[csimp]`, and proves `padF msg = pad RATE msg`.

It also proves the in-place sponge `keccak256U` equal to `keccak256`, and does not install it.

`Keccak/FastProofI.lean` proves that the bit-interleaved sponge `keccak256I` equals `keccak256`.

That holds whenever `(padF msg).size < USize.size`.

`FastProofI.lean` installs `keccak256IG` for `keccak256` with `@[csimp]`.

`keccak256IG` runs the body of `keccak256I` when the padded message is shorter than `2^31 - 1`.

Otherwise it runs the specification.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak.Fast
open EthLib.Cryptography.Hash.Keccak

/-- `RC[i]` as match arms, so it compiles to a switch rather than a boxed-array lookup. -/
def rcAt : UInt32 → UInt64""")
for k, c in enumerate(RC): w(f"  | {k} => 0x{c:016X}")
w("  | _ => 0\n")
# loop version: one round per tail call, fuel n, round index i.
w(f"/-- `n` more rounds from round `i`, one round per tail call. -/")
w(pack("def loop1 : Nat → UInt32 → (", [f"a{k}" for k in L], " ", "    ", " : UInt64) → State"))
w(pack("  | 0, _, ", [f"a{k}" for k in L], ", ", "      ", " =>"))
w(pack("    ⟨", [f"a{k}" for k in L], ", ", "      ", "⟩"))
w(pack("  | n + 1, i, ", [f"a{k}" for k in L], ", ", "      ", " =>"))
lines += rnd("a", "e", "", "rcAt i", "    ")
w(pack("    loop1 n (i + 1) ", [f"e{k}" for k in L], " ", "      ") + "\n")
# loop2: two rounds per tail call
w(f"/-- `2n` more rounds from round `i`, two rounds per tail call. -/")
w(pack("def loop2 : Nat → UInt32 → (", [f"a{k}" for k in L], " ", "    ", " : UInt64) → State"))
w(pack("  | 0, _, ", [f"a{k}" for k in L], ", ", "      ", " =>"))
w(pack("    ⟨", [f"a{k}" for k in L], ", ", "      ", "⟩"))
w(pack("  | n + 1, i, ", [f"a{k}" for k in L], ", ", "      ", " =>"))
lines += rnd("a", "b", "_0", "rcAt i", "    ")
lines += rnd("b", "e", "_1", "rcAt (i + 1)", "    ")
w(pack("    loop2 n (i + 2) ", [f"e{k}" for k in L], " ", "      ") + "\n")
w("""/-- Keccak-f[1600], one round per tail call. -/
def keccakF1 (A : State) : State :=
  loop1 24 0 A.a0 A.a1 A.a2 A.a3 A.a4 A.a5 A.a6 A.a7 A.a8 A.a9 A.a10 A.a11 A.a12 A.a13 A.a14
    A.a15 A.a16 A.a17 A.a18 A.a19 A.a20 A.a21 A.a22 A.a23 A.a24

/-- Keccak-f[1600], two rounds per tail call. -/
def keccakF2 (A : State) : State :=
  loop2 12 0 A.a0 A.a1 A.a2 A.a3 A.a4 A.a5 A.a6 A.a7 A.a8 A.a9 A.a10 A.a11 A.a12 A.a13 A.a14
    A.a15 A.a16 A.a17 A.a18 A.a19 A.a20 A.a21 A.a22 A.a23 A.a24
""")
w("""/-! ## Padding and the digest of Keccak-256 -/

def zeros136 : ByteArray := ⟨Array.replicate 136 0⟩

/-- `pad RATE msg` built with byte-array copies instead of a boxed `Array UInt8`. -/
def padF (msg : ByteArray) : ByteArray :=
  let k := RATE - msg.size % RATE
  let b := (ByteArray.emptyWithCapacity (msg.size + k)).append msg
  let b := zeros136.copySlice 0 b b.size k
  let b := b.set! msg.size (b.get! msg.size ||| 0x01)
  b.set! (b.size - 1) (b.get! (b.size - 1) ||| 0x80)

/-- The 32 digest bytes of lanes 0 to 3, least significant first, in one array. -/
def squeezeF (S : State) : Vector UInt8 DIGEST_LEN :=
  let a := S.a0; let b := S.a1; let c := S.a2; let d := S.a3
  ⟨#[a.toUInt8, (a >>> 8).toUInt8, (a >>> 16).toUInt8, (a >>> 24).toUInt8,
     (a >>> 32).toUInt8, (a >>> 40).toUInt8, (a >>> 48).toUInt8, (a >>> 56).toUInt8,
     b.toUInt8, (b >>> 8).toUInt8, (b >>> 16).toUInt8, (b >>> 24).toUInt8,
     (b >>> 32).toUInt8, (b >>> 40).toUInt8, (b >>> 48).toUInt8, (b >>> 56).toUInt8,
     c.toUInt8, (c >>> 8).toUInt8, (c >>> 16).toUInt8, (c >>> 24).toUInt8,
     (c >>> 32).toUInt8, (c >>> 40).toUInt8, (c >>> 48).toUInt8, (c >>> 56).toUInt8,
     d.toUInt8, (d >>> 8).toUInt8, (d >>> 16).toUInt8, (d >>> 24).toUInt8,
     (d >>> 32).toUInt8, (d >>> 40).toUInt8, (d >>> 48).toUInt8, (d >>> 56).toUInt8], rfl⟩
""")
w("""/-! ## Lane reads without bounds checks or `Nat` arithmetic -/

theorem idx_lt {p s : Nat} (h : p + 136 ≤ s) (c : Nat) (hc : c < 136) :
    (USize.ofNat p + USize.ofNat c).toNat < s := by
  rw [USize.toNat_add]
  have h1 :=
    Nat.mod_le ((USize.ofNat p).toNat + (USize.ofNat c).toNat) (2 ^ System.Platform.numBits)
  have h2 : (USize.ofNat p).toNat ≤ p := by rw [USize.toNat_ofNat']; exact Nat.mod_le _ _
  have h3 : (USize.ofNat c).toNat ≤ c := by rw [USize.toNat_ofNat']; exact Nat.mod_le _ _
  omega

/-- Byte `c` of the block at `p`, as a `UInt32`, read in place. -/
@[inline] def rdb (bytes : @& ByteArray) (p : Nat) (h : p + 136 ≤ bytes.size) (q : USize)
    (hq : q = USize.ofNat p) (c : Nat) (hc : c < 136) : UInt32 :=
  (bytes.uget (q + USize.ofNat c) (hq ▸ idx_lt h c hc)).toUInt32

/-- The little-endian word of bytes `c` to `c + 3` of the block at `p`. -/
@[inline] def lane32 (bytes : @& ByteArray) (p : Nat) (h : p + 136 ≤ bytes.size) (q : USize)
    (hq : q = USize.ofNat p) (c : Nat) (hc : c + 4 ≤ 136) : UInt32 :=
  rdb bytes p h q hq c (by omega) ||| rdb bytes p h q hq (c + 1) (by omega) <<< 8 |||
    rdb bytes p h q hq (c + 2) (by omega) <<< 16 ||| rdb bytes p h q hq (c + 3) (by omega) <<< 24
""")
w("end EthLib.Cryptography.Hash.Keccak.Fast")
open(sys.argv[1], "w").write("\n".join(lines) + "\n")
