module

public import EthLib.Base.Bytes.Spec
public import EthLib.Base.Bytes.Fast

/-!
# Fixed-length bytes

The specification is `Bytes/Spec.lean`; every proof reasons about it.

`Bytes/Fast.lean` reads a slice of a buffer in one pass, and proves the read equal to `readBytes`.

It installs the read with `@[csimp]`.

So compiled code that calls `readBytes` copies the slice once, not the whole buffer once per byte.
-/
