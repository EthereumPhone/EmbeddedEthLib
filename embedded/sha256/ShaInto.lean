import EthLib.Cryptography.Hash.Sha256

/-!
# SHA-256 benchmark of `hashInto`

A Cortex-M33 benchmark entry, not part of EthLib, built by `sha256/build.sh into`.

It calls `Sha256.Zsf.hashInto` with one reused, exclusive 32-byte buffer.

So every hash writes its digest in place and allocates nothing.

Messages are read through `pq_load` from a volatile blob (the leanSPHINCS known answers).

So nothing can be folded at compile time.

The cost per hash is the difference of an 11-hash and a 1-hash segment, divided by 10.

That is the method of the C reference (`sha256/ref.c`, `board/sha/ref_board.c`).

Segments (`pq_mark`): 1->2 one 3-byte hash, 3->4 eleven, 5->6 one 64-byte hash, 7->8 eleven.

Then 9->10 one 1,072-byte hash and 11->12 eleven.

Reports 1 to 6 are the buffer after each of those segments.

So 1 and 2 are the digest of the 3-byte message, 3 and 4 of the 64-byte one, 5 and 6 of the longest.
-/

open EthLib.Cryptography.Hash

@[extern "pq_mark"] opaque mark (k : UInt32) : BaseIO Unit
@[extern "pq_load"] opaque load (off len : UInt32) : BaseIO ByteArray
@[extern "pq_report_bytes"] opaque reportBytes (tag : UInt32) (b : @& ByteArray) : BaseIO Unit

def rep : Nat → ByteArray → ByteArray → ByteArray
  | 0, _, out => out
  | k + 1, m, out => rep k m (Sha256.Zsf.hashInto m out)

@[export lean_fw_main]
def fwMain (_ : Unit) : BaseIO Unit := do
  let m3 ← load 0 3
  let m64 ← load 0 64
  let m1072 ← load 64 1072
  let o ← load 0 32
  mark 1
  let o := rep 1 m3 o
  mark 2
  reportBytes 1 o
  mark 3
  let o := rep 11 m3 o
  mark 4
  reportBytes 2 o
  mark 5
  let o := rep 1 m64 o
  mark 6
  reportBytes 3 o
  mark 7
  let o := rep 11 m64 o
  mark 8
  reportBytes 4 o
  mark 9
  let o := rep 1 m1072 o
  mark 10
  reportBytes 5 o
  mark 11
  let o := rep 11 m1072 o
  mark 12
  reportBytes 6 o
