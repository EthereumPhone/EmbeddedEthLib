# Appends a bit-interleaved (2 x UInt32 per lane) Keccak to Fast.lean, after gen.py has written it.
# gen_proofI.py imports `rnd` from here. Run regen.py rather than this script alone.
RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
RHO = [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14]
PI = [0,6,12,18,24,3,9,10,16,22,1,7,13,19,20,4,5,11,17,23,2,8,14,15,21]
def split(v):
    e = o = 0
    for i in range(32):
        e |= ((v >> (2*i)) & 1) << i
        o |= ((v >> (2*i+1)) & 1) << i
    return e, o
def r32(x, m): return x if m == 0 else f"rol32 {x} {m}"
def rot(te, to, n):
    if n % 2 == 0: return r32(te, n//2), r32(to, n//2)
    m = (n - 1) // 2
    return r32(to, m + 1), r32(te, m)
def rnd(i, o, s, rce, rco, ind):
    out = []
    for h in "eo":
        for x in range(5):
            out.append(f"{ind}let c{x}{h}{s} := {i}{x}{h} ^^^ {i}{x+5}{h} ^^^ {i}{x+10}{h} ^^^ {i}{x+15}{h} ^^^ {i}{x+20}{h}")
    for x in range(5):
        out.append(f"{ind}let d{x}e{s} := c{(x+4)%5}e{s} ^^^ rol32 c{(x+1)%5}o{s} 1")
        out.append(f"{ind}let d{x}o{s} := c{(x+4)%5}o{s} ^^^ c{(x+1)%5}e{s}")
    for k in range(25):
        te, to = f"({i}{k}e ^^^ d{k%5}e{s})", f"({i}{k}o ^^^ d{k%5}o{s})"
        re_, ro = rot(te, to, RHO[k])
        out.append(f"{ind}let r{k}e{s} := {re_}")
        out.append(f"{ind}let r{k}o{s} := {ro}")
    for h, rc in (("e", rce), ("o", rco)):
        for y in range(5):
            for x in range(5):
                k = 5*y + x
                p = lambda xx: f"r{PI[5*y + xx % 5]}{h}{s}"
                e = f"{p(x)} ^^^ (~~~{p(x+1)} &&& {p(x+2)})"
                if k == 0: e = f"({e}) ^^^ {rc}"
                out.append(f"{ind}let {o}{k}{h} := {e}")
    return out
L = []
w = L.append
names = lambda p: " ".join(f"{p}{k}{h}" for k in range(25) for h in "eo")
commas = lambda p: ", ".join(f"{p}{k}{h}" for k in range(25) for h in "eo")
w("""/-! ## Bit-interleaved form: each lane as two `UInt32`, its even and its odd bits

A 64-bit rotation by `2m` rotates both halves by `m`; by `2m + 1` it swaps them and rotates by `m + 1` and `m`. So every operation of a round is a 32-bit operation, which Thumb-2 does in one instruction, with the rotations folded into the operands of `eor`/`bic`. -/

/-- The state in bit-interleaved form: field `kE` holds the even bits of lane `k`, `kO` the odd bits. -/
structure StateI where
  (""" + " ".join(f"e{k} o{k}" for k in range(25)) + """ : UInt32)

@[inline] def rol32 (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))
""")
w("def rcE : UInt32 → UInt32")
for k, c in enumerate(RC): w(f"  | {k} => 0x{split(c)[0]:08X}")
w("  | _ => 0\n")
w("def rcO : UInt32 → UInt32")
for k, c in enumerate(RC): w(f"  | {k} => 0x{split(c)[1]:08X}")
w("  | _ => 0\n")
sig = " ".join(f"a{k}e a{k}o" for k in range(25))
w(f"""/-- `2n` more rounds from round `i`, two per tail call, on the interleaved lanes. -/
def loopI2 : Nat → UInt32 → ({sig} : UInt32) → StateI
  | 0, _, {commas('a')} => ⟨{commas('a')}⟩
  | n + 1, i, {commas('a')} =>""")
L.extend(rnd("a", "b", "_0", "rcE i", "rcO i", "    "))
L.extend(rnd("b", "z", "_1", "rcE (i + 1)", "rcO (i + 1)", "    "))
w(f"    loopI2 n (i + 2) {names('z')}\n")
w("""/-- Keccak-f[1600] on the interleaved state. -/
def keccakPI (S : StateI) : StateI :=
  loopI2 12 0 """ + " ".join(f"S.e{k} S.o{k}" for k in range(25)) + """

/-- The even bits of the 64-bit lane `hi:lo`, compressed into a word. -/
@[inline] def shuf (x : UInt32) : UInt32 :=
  let t := (x ^^^ (x >>> 1)) &&& 0x22222222
  let x := x ^^^ t ^^^ (t <<< 1)
  let t := (x ^^^ (x >>> 2)) &&& 0x0C0C0C0C
  let x := x ^^^ t ^^^ (t <<< 2)
  let t := (x ^^^ (x >>> 4)) &&& 0x00F000F0
  let x := x ^^^ t ^^^ (t <<< 4)
  let t := (x ^^^ (x >>> 8)) &&& 0x0000FF00
  x ^^^ t ^^^ (t <<< 8)

/-- The inverse of `shuf`: the same delta swaps in reverse order. -/
@[inline] def unshuf (x : UInt32) : UInt32 :=
  let t := (x ^^^ (x >>> 8)) &&& 0x0000FF00
  let x := x ^^^ t ^^^ (t <<< 8)
  let t := (x ^^^ (x >>> 4)) &&& 0x00F000F0
  let x := x ^^^ t ^^^ (t <<< 4)
  let t := (x ^^^ (x >>> 2)) &&& 0x0C0C0C0C
  let x := x ^^^ t ^^^ (t <<< 2)
  let t := (x ^^^ (x >>> 1)) &&& 0x22222222
  x ^^^ t ^^^ (t <<< 1)

@[inline] def ilvE (lo hi : UInt32) : UInt32 := (shuf lo &&& (0xFFFF : UInt32)) ||| (shuf hi <<< 16)
@[inline] def ilvO (lo hi : UInt32) : UInt32 := (shuf lo >>> 16) ||| (shuf hi &&& (0xFFFF0000 : UInt32))
@[inline] def dlvLo (e o : UInt32) : UInt32 := unshuf ((e &&& (0xFFFF : UInt32)) ||| (o <<< 16))
@[inline] def dlvHi (e o : UInt32) : UInt32 := unshuf ((e >>> 16) ||| (o &&& (0xFFFF0000 : UInt32)))
@[inline] def ilvE64 (v : UInt64) : UInt32 := ilvE v.toUInt32 (v >>> 32).toUInt32
@[inline] def ilvO64 (v : UInt64) : UInt32 := ilvO v.toUInt32 (v >>> 32).toUInt32
@[inline] def dlv64 (e o : UInt32) : UInt64 := (dlvLo e o).toUInt64 ||| ((dlvHi e o).toUInt64 <<< 32)
""")
absorb = ",\n      ".join(
    f"S.e{k} ^^^ ilvE (lane32 bytes p h q rfl {8*k} (by decide)) (lane32 bytes p h q rfl {8*k+4} (by decide)), "
    f"S.o{k} ^^^ ilvO (lane32 bytes p h q rfl {8*k} (by decide)) (lane32 bytes p h q rfl {8*k+4} (by decide))"
    for k in range(17))
rest = ", ".join(f"S.e{k}, S.o{k}" for k in range(17, 25))
w(f"""/-- Absorb `n` blocks of 136 bytes from `p` on into the interleaved state. -/
def absorbI (bytes : @& ByteArray) : (n p : Nat) → p + 136 * n ≤ bytes.size → StateI → StateI
  | 0, _, _, S => S
  | n + 1, p, hp, S =>
    have h : p + 136 ≤ bytes.size := by omega
    let q := USize.ofNat p
    absorbI bytes n (p + 136) (by omega) (keccakPI ⟨
      {absorb},
      {rest}⟩)

/-- The 32 digest bytes from interleaved lanes 0 to 3. -/
def squeezeI (S : StateI) : Vector UInt8 DIGEST_LEN :=
  let a0 := dlvLo S.e0 S.o0; let a1 := dlvHi S.e0 S.o0
  let b0 := dlvLo S.e1 S.o1; let b1 := dlvHi S.e1 S.o1
  let c0 := dlvLo S.e2 S.o2; let c1 := dlvHi S.e2 S.o2
  let d0 := dlvLo S.e3 S.o3; let d1 := dlvHi S.e3 S.o3
  ⟨#[{", ".join(f"({v} >>> {8*j}).toUInt8" for v in ["a0","a1","b0","b1","c0","c1","d0","d1"] for j in range(4))}], rfl⟩

def zeroI : StateI := ⟨{", ".join("0" for _ in range(50))}⟩

/-- Keccak-256 with the interleaved state kept across blocks. -/
def keccak256I (msg : ByteArray) : Vector UInt8 DIGEST_LEN :=
  let padded := padF msg
  squeezeI (absorbI padded (padded.size / 136) 0
    (by have := Nat.mul_div_le padded.size 136; omega) zeroI)
""")
if __name__ == "__main__":
    import sys
    src = open(sys.argv[1]).read()
    end = "end EthLib.Cryptography.Hash.Keccak.Fast"
    src = src.replace(end, "\n".join(L) + "\n" + end)
    open(sys.argv[1], "w").write(src)
