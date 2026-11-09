module

public import EthLib.Base.Bytes.Spec
public import EthLib.Base.Bytes.Fast

/-!
# Fixed-length bytes

The specification is `Bytes/Spec.lean`; every proof reasons about it.

`Bytes/Fast.lean` reads a slice of a buffer in one pass, proves the read equal to `readBytes`, and installs it with `@[csimp]`, so compiled code that calls `readBytes` copies the slice once instead of copying the whole buffer once per byte.
-/
