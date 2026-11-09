module

public import EthLib.Cryptography.Hash.Sha256.Spec
public import EthLib.Cryptography.Hash.Sha256.ZsfProof.Main

/-!
# SHA-256

The specification is `Sha256/Spec.lean`, FIPS 180-4 step by step; every proof reasons about it.

`Sha256/Zsf.lean` computes the same function without allocation on 32-bit targets and does not
import the specification. `Sha256/ZsfProof/` proves the two equal (`Zsf.hashInto_eq`) and
`Sha256/ZsfProof/Main.lean` installs the fast form with `@[csimp]`, so compiled code that calls
`sha256`, `Sha256.hash` or `Sha256.hash32` runs it. Zero-allocation callers use
`Sha256.Zsf.hashInto message buffer` directly.
-/
