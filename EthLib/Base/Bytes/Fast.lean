module

public import EthLib.Base.Bytes.Spec

/-!
# Fixed-length bytes, fast reads

`readBytes` is `Vector.ofFn fun i => b.data[offset + i]`.

In compiled code `b.data` converts the whole `ByteArray` to a boxed `Array UInt8`.

That conversion (`lean_byte_array_data`) runs once per byte read.

So a read of `n` bytes from a buffer of `s` bytes costs `n * s`.

`readBytesP` copies the slice once (`ByteArray.copySlice`, `lean_byte_array_copy_slice`).

It converts only that slice, so a read costs `n`.

`readBytes_eq_readBytesP` proves the two equal and installs the fast form with `@[csimp]`.

The kernel still reasons about `readBytes`.
-/

public section

namespace EthLib.Base

/-- The one-pass copy is the slice `[offset, offset + n)` of the buffer. -/
theorem copySlice_emptyWithCapacity (b : ByteArray) (offset n : Nat) :
    b.copySlice offset (ByteArray.emptyWithCapacity n) 0 n = b.extract offset (offset + n) := by
  simp only [ByteArray.extract, Nat.add_sub_cancel_left]; rfl

/-- `readBytes`, read in one pass: the slice is copied out of the buffer once, then boxed.

The destination is an empty buffer with room for exactly `n` bytes, so the copy never grows it. -/
def readBytesP (b : ByteArray) (offset n : Nat) (h : offset + n ≤ b.size) : Vector UInt8 n :=
  ⟨(b.copySlice offset (ByteArray.emptyWithCapacity n) 0 n).data, by
    rw [copySlice_emptyWithCapacity, ByteArray.data_extract, Array.size_extract]
    simp only [ByteArray.size] at h
    omega⟩

/-- Compiled code that calls `readBytes` runs `readBytesP`.

The kernel still reasons about `readBytes`. -/
@[csimp] theorem readBytes_eq_readBytesP : @readBytes = @readBytesP := by
  funext b offset n h
  apply Vector.ext
  intro i hi
  simp only [readBytes, readBytesP, Vector.getElem_ofFn, Vector.getElem_mk,
    copySlice_emptyWithCapacity, ByteArray.data_extract, Array.getElem_extract]

end EthLib.Base
