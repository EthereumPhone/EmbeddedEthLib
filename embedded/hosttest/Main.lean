module

import EthLib.Cryptography.Hash.Sha256
import EthLib.Cryptography.Hash.Keccak
import EthLib.Cryptography.Sphincs

/-! Checks this fork's compiled code against `tests/cryptography`.

It calls the public functions of the library, the same calls the C exports make.

* SHA-256: `Hash.sha256`, `Sha256.hash`, `Sha256.hash32` and `Sha256.Zsf.hashInto`.

* `hashInto` runs with a fresh buffer, with an empty one and with one reused buffer.

* Keccak: `keccak256`, `keccak512`, and `keccakF` on the state read as the C export reads it.

* leanSPHINCS: `keyGen`, `sign` with `encodeSignature`, and decoding with `verify`.

Where a vector says `null`, the C export rejects the length of an input.

The test then checks that the input is rejected.

Usage: `hosttest [tests/cryptography directory] [--no-sign]`. -/

open EthLib.Cryptography

def hexVal (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

def parseHex (s : String) : Option ByteArray := Id.run do
  let cs := s.toList
  let cs := if cs.take 2 == ['0', 'x'] then cs.drop 2 else cs
  let cs := cs.toArray
  if cs.size % 2 != 0 then return none
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    match hexVal cs[2 * i]!, hexVal cs[2 * i + 1]! with
    | some hi, some lo => out := out.push (hi * 16 + lo)
    | _, _ => return none
  return some out

/-- The value of `key:` in a vector file, without quotes. -/
def field (text : String) (key : String) : Option String :=
  let pre := (key ++ ": ").toList
  (text.splitOn "\n").findSome? fun line =>
    let t := line.toList.dropWhile (· == ' ')
    if pre.isPrefixOf t then
      let junk (c : Char) : Bool := c == ' ' || c == '\'' || c == '\r'
      let v := (((t.drop pre.length).dropWhile (· == ' ')).reverse.dropWhile junk).reverse
      some (String.ofList (if v.head? == some '\'' then v.drop 1 else v))
    else none

def hexField (text key : String) : Option ByteArray := (field text key).bind parseHex

structure Tally where
  cases : Nat := 0
  checks : Nat := 0
  failures : Array String := #[]

def Tally.check (t : Tally) (name : String) (ok : Bool) : Tally :=
  { t with checks := t.checks + 1, failures := if ok then t.failures else t.failures.push name }

def caseDirs (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← dir.readDir
  let ds := entries.filter (fun e => e.fileName != "format.md") |>.map (·.path)
  return ds.qsort (fun a b => a.toString < b.toString)

def toBA {n : Nat} (v : Vector UInt8 n) : ByteArray := ⟨v.toArray⟩

def vec? (n : Nat) (b : ByteArray) : Option (Vector UInt8 n) :=
  if h : b.size = n then some ⟨b.data, h⟩ else none

/-- Keccak-f[1600] on a 200-byte state, lane `i` at bytes `8i..8i+7`, least significant first. -/
def permute (state : ByteArray) : Option ByteArray := Id.run do
  if state.size != 200 then return none
  let lane (i : Nat) : UInt64 := Hash.Keccak.Internal.laneAt state (8 * i)
  let A : Hash.Keccak.State := ⟨lane 0, lane 1, lane 2, lane 3, lane 4, lane 5, lane 6, lane 7,
    lane 8, lane 9, lane 10, lane 11, lane 12, lane 13, lane 14, lane 15, lane 16, lane 17, lane 18,
    lane 19, lane 20, lane 21, lane 22, lane 23, lane 24⟩
  let B := Hash.Keccak.keccakF A
  let out := [B.a0, B.a1, B.a2, B.a3, B.a4, B.a5, B.a6, B.a7, B.a8, B.a9, B.a10, B.a11, B.a12,
    B.a13, B.a14, B.a15, B.a16, B.a17, B.a18, B.a19, B.a20, B.a21, B.a22, B.a23,
    B.a24].flatMap Hash.Keccak.Internal.bytesOfLane
  return some ⟨out.toArray⟩

def runSha256 (root : System.FilePath) (t : Tally) : IO Tally := do
  let mut t := t
  let mut reused := ByteArray.mk (Array.replicate 32 0)
  for d in ← caseDirs (root / "sha256" / "hash") do
    let text ← IO.FS.readFile (d / "data.yaml")
    let some msg := hexField text "message" | throw (IO.userError s!"{d}: no message")
    let some want := hexField text "output" | throw (IO.userError s!"{d}: no output")
    let n := d.fileName.getD "?"
    t := { t with cases := t.cases + 1 }
    t := t.check s!"Hash.sha256 {n}" (Hash.sha256 msg == want)
    t := t.check s!"Sha256.hash {n}" (Hash.Sha256.hash msg == want)
    t := t.check s!"Sha256.hash32 {n}" (ByteArray.mk (Hash.Sha256.hash32 msg).toArray == want)
    t := t.check s!"hashInto fresh {n}"
      (Hash.Sha256.Zsf.hashInto msg (ByteArray.mk (Array.replicate 32 0)) == want)
    t := t.check s!"hashInto empty {n}" (Hash.Sha256.Zsf.hashInto msg ByteArray.empty == want)
    reused := Hash.Sha256.Zsf.hashInto msg reused
    t := t.check s!"hashInto reused {n}" (reused == want)
  return t

def runKeccak (root : System.FilePath) (t : Tally) : IO Tally := do
  let mut t := t
  let fs : List (String × (ByteArray → ByteArray)) :=
    [("hash", fun m => toBA (Hash.Keccak.keccak256 m)),
     ("hash_512", fun m => toBA (Hash.Keccak.keccak512 m))]
  for (sub, f) in fs do
    for d in ← caseDirs (root / "keccak" / sub) do
      let text ← IO.FS.readFile (d / "data.yaml")
      let some msg := hexField text "message" | throw (IO.userError s!"{d}: no message")
      let some want := hexField text "output" | throw (IO.userError s!"{d}: no output")
      t := { t with cases := t.cases + 1 }
      t := t.check s!"keccak {sub} {d.fileName.getD "?"}" (f msg == want)
  for d in ← caseDirs (root / "keccak" / "permutation") do
    let text ← IO.FS.readFile (d / "data.yaml")
    let some st := hexField text "state" | throw (IO.userError s!"{d}: no state")
    t := { t with cases := t.cases + 1 }
    t := t.check s!"keccakF {d.fileName.getD "?"}" (permute st == hexField text "output")
  return t

open EthLib.Cryptography.Sphincs in
def runSphincs (root : System.FilePath) (doSign : Bool) (t : Tally) : IO Tally := do
  let mut t := t
  for d in ← caseDirs (root / "sphincs" / "key_gen") do
    let text ← IO.FS.readFile (d / "data.yaml")
    let some seedB := hexField text "seed" | throw (IO.userError s!"{d}: no seed")
    let got := (vec? 32 seedB).map fun seed => encodePublicKey (keyGen seed).2
    t := { t with cases := t.cases + 1 }
    t := t.check s!"sphincs key_gen {d.fileName.getD "?"}" (got == hexField text "output")
  if doSign then
    for d in ← caseDirs (root / "sphincs" / "sign") do
      let text ← IO.FS.readFile (d / "data.yaml")
      let some seedB := hexField text "seed" | throw (IO.userError s!"{d}: no seed")
      let some msgB := hexField text "message" | throw (IO.userError s!"{d}: no message")
      let got : Option ByteArray := do
        let seed ← vec? 32 seedB
        let msg ← vec? 32 msgB
        match sign ⟨seed⟩ msg with
        | .ok s => some (encodeSignature s)
        | .error _ => none
      t := { t with cases := t.cases + 1 }
      t := t.check s!"sphincs sign {d.fileName.getD "?"}" (got == hexField text "output")
  for d in ← caseDirs (root / "sphincs" / "verify") do
    let text ← IO.FS.readFile (d / "data.yaml")
    let some pkB := hexField text "public_key" | throw (IO.userError s!"{d}: no public_key")
    let some msgB := hexField text "message" | throw (IO.userError s!"{d}: no message")
    let some sigB := hexField text "signature" | throw (IO.userError s!"{d}: no signature")
    let want : Option Bool := match field text "output" with
      | some "true" => some true | some "false" => some false | _ => none
    let got : Option Bool := match decodePublicKey pkB, vec? 32 msgB, decodeSignature sigB with
      | .ok pk, some msg, .ok sig => some (verify pk msg sig)
      | _, _, _ => none
    t := { t with cases := t.cases + 1 }
    t := t.check s!"sphincs verify {d.fileName.getD "?"}" (got == want)
  return t

public def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := (args.filter (!·.startsWith "--")).headD "../../tests/cryptography"
  let sign := !args.contains "--no-sign"
  let mut t : Tally := {}
  for (name, step) in [("sha256", runSha256 root), ("keccak", runKeccak root),
      ("sphincs", runSphincs root sign)] do
    let t0 ← IO.monoMsNow
    let before := t.cases
    t ← step t
    IO.println s!"{name}: {t.cases - before} cases, {(← IO.monoMsNow) - t0} ms"
  for f in t.failures do IO.println s!"FAIL {f}"
  IO.println s!"hosttest: cases={t.cases} checks={t.checks} failures={t.failures.size}"
  return if t.failures.isEmpty && t.cases > 0 then 0 else 1
