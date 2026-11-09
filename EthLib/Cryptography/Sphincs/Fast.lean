module

public import EthLib.Cryptography.Sphincs.Sign

/-!
# Executable leanSPHINCS signing and key generation without subtree recomputation

`Merkle.path` builds every sibling subtree on its own, and `Merkle.root` builds the tree again, so the specification's `sign` evaluates 3,069 one-time-key leaves where 1,536 suffice, and every FORS leaf twice. The specification is generic over a monad so that a proof can count oracle queries; "compute once" and "recompute" agree only for the pure instance, `hashId` in `Id`.

This module targets that pure instance only:

- `Merkle.Fast.rootAndPath` builds a tree level by level, once, and returns its root and the path of one leaf. `keyGenFast` uses it.
- `Merkle.Packed.levels` keeps every level of a tree packed in `ByteArray`s, 16 bytes a digest instead of a boxed `Vector UInt8 16` (about 80 bytes on a 32-bit target). It holds the top tree, whose leaf is not known when its root is needed (`PK.root` feeds `H_msg`, which picks the leaf):
  2,047 digests in 32,752 bytes.
- `treeRootAndPathDF` and `forsOpenAndRootDF` build a tree whose leaf is known depth first: the specification's own `path`, whose sibling subtrees cover every leaf but the key's, then the climb from that leaf. Every leaf and node is computed once, and at most one node per level is held.
- `signFast` is `sign` with every tree built once and the packed top tree released before FORS (`signBelowTop` is `@[noinline]` so the compiler cannot sink the top path's read past it). All other hash calls (key expansion, `PRF_msg`, `H_msg`, the FORS opening secrets, the WOTS+C counter search and chains, `T_k`) are the specification's own functions at `hashId`; the FORS leaf under each opening is `F` of the opening's secret, so its `PRF` call is not repeated.

`FastEq.lean` proves `sign = signFast` and `keyGen = keyGenFast`.

It installs the first with `@[csimp]`.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle.Fast

variable {α : Type} [Inhabited α]

/-- `leaves 0, ..., leaves (n - 1)`, pushed in order onto `acc`, from index `i`. -/
def leafLevelGo (leaves : Nat → α) (n : Nat) (i : Nat) (acc : Array α) : Array α :=
  if i < n then leafLevelGo leaves n (i + 1) (acc.push (leaves i)) else acc
termination_by n - i

/-- Level 0 of a tree with `n` leaves. -/
@[inline] def leafLevel (leaves : Nat → α) (n : Nat) : Array α :=
  leafLevelGo leaves n 0 (Array.mkEmpty n)

/-- Nodes `j, ..., n - 1` of level `z + 1`, from level `z` (`prev`), pushed onto `acc`. -/
def parentLevelGo (hash : Nat → Nat → α → α → α) (z : Nat) (prev : Array α) (n : Nat) (j : Nat)
    (acc : Array α) : Array α :=
  if j < n then
    parentLevelGo hash z prev n (j + 1) (acc.push (hash (z + 1) j prev[2 * j]! prev[2 * j + 1]!))
  else acc
termination_by n - j

/-- Level `z + 1`, `n` nodes, from level `z`. -/
@[inline] def parentLevel (hash : Nat → Nat → α → α → α) (z : Nat) (prev : Array α) (n : Nat) :
    Array α :=
  parentLevelGo hash z prev n 0 (Array.mkEmpty n)

/-- Climb `k` levels from level `z` (`cur`, `2^k` nodes), pushing the sibling of the ancestor of leaf `e` at each level onto `acc`. Returns the root and the siblings, level `z` first. -/
def climbLevels (hash : Nat → Nat → α → α → α) (e : Nat) :
    (k z : Nat) → (cur acc : Array α) → α × Array α
  | 0, _, cur, acc => (cur[0]!, acc)
  | k + 1, z, cur, acc =>
    climbLevels hash e k (z + 1) (parentLevel hash z cur (2 ^ k)) (acc.push cur[(e >>> z) ^^^ 1]!)

/-- The root of the tree of height `h` and the path of leaf `e`, from the leaf up, with every leaf and node computed once. Equals `(Merkle.root hash leaves h, Merkle.path hash leaves h e)` in `Id` for `e < 2^h`. -/
def rootAndPath (hash : Nat → Nat → α → α → α) (leaves : Nat → α) (h e : Nat) : α × Vector α h :=
  let (r, p) := climbLevels hash e h 0 (leafLevel leaves (2 ^ h)) (Array.mkEmpty h)
  (r, Vector.ofFn fun i => p[i.val]!)

/-- Every level of the tree, level 0 first, from level `z` (`cur`, `2^k` nodes). -/
def allLevelsGo (hash : Nat → Nat → α → α → α) :
    (k z : Nat) → (cur : Array α) → (acc : Array (Array α)) → Array (Array α)
  | 0, _, cur, acc => acc.push cur
  | k + 1, z, cur, acc => allLevelsGo hash k (z + 1) (parentLevel hash z cur (2 ^ k)) (acc.push cur)

/-- Every level of the tree of height `h`, level 0 (the leaves) first and the root's level last. -/
def allLevels (hash : Nat → Nat → α → α → α) (leaves : Nat → α) (h : Nat) : Array (Array α) :=
  allLevelsGo hash h 0 (leafLevel leaves (2 ^ h)) (Array.mkEmpty (h + 1))

/-- The root, from the levels of a tree of height `h`. -/
@[inline] def levelsRoot (levels : Array (Array α)) (h : Nat) : α :=
  levels[h]![0]!

/-- The path of leaf `e`, from the levels of a tree of height `h`. -/
@[inline] def levelsPath (levels : Array (Array α)) (h e : Nat) : Vector α h :=
  Vector.ofFn fun z => levels[z.val]![(e >>> z.val) ^^^ 1]!

end EthLib.Cryptography.Merkle.Fast

/-! ## Packed levels

A digest held in an `Array` is a boxed `Vector UInt8 16`: about 80 bytes on a 32-bit target. A packed row holds `n` digests of `k` bytes in one `ByteArray` of `k * n` bytes. -/

namespace EthLib.Cryptography.Merkle.Packed

variable {k : Nat}

/-- Push the bytes `d[i], ..., d[k - 1]` onto `buf`. -/
def pushGo (buf : ByteArray) (d : Vector UInt8 k) (i : Nat) : ByteArray :=
  if h : i < k then pushGo (buf.push d[i]) d (i + 1) else buf
termination_by k - i

/-- Push the `k` bytes of `d` onto `buf`. -/
@[inline] def pushD (buf : ByteArray) (d : Vector UInt8 k) : ByteArray :=
  pushGo buf d 0

/-- Digest `j` of a packed row: bytes `k * j` to `k * j + k - 1`. -/
@[inline] def getD (buf : ByteArray) (j : Nat) : Vector UInt8 k :=
  Vector.ofFn fun i => buf.get! (k * j + i.val)

/-- Leaves `i, ..., n - 1`, packed onto `acc`. -/
def leafRowGo (leaves : Nat → Vector UInt8 k) (n i : Nat) (acc : ByteArray) : ByteArray :=
  if i < n then leafRowGo leaves n (i + 1) (pushD acc (leaves i)) else acc
termination_by n - i

/-- Level 0 of a tree with `n` leaves, packed. -/
@[inline] def leafRow (leaves : Nat → Vector UInt8 k) (n : Nat) : ByteArray :=
  leafRowGo leaves n 0 (ByteArray.emptyWithCapacity (k * n))

/-- Nodes `j, ..., n - 1` of level `z + 1`, from the packed level `z` (`prev`), packed onto `acc`. -/
def parentRowGo (hash : Nat → Nat → Vector UInt8 k → Vector UInt8 k → Vector UInt8 k) (z : Nat)
    (prev : ByteArray) (n j : Nat) (acc : ByteArray) : ByteArray :=
  if j < n then
    parentRowGo hash z prev n (j + 1)
      (pushD acc (hash (z + 1) j (getD prev (2 * j)) (getD prev (2 * j + 1))))
  else acc
termination_by n - j

/-- Level `z + 1`, `n` nodes, from the packed level `z`, packed. -/
@[inline] def parentRow (hash : Nat → Nat → Vector UInt8 k → Vector UInt8 k → Vector UInt8 k)
    (z : Nat) (prev : ByteArray) (n : Nat) : ByteArray :=
  parentRowGo hash z prev n 0 (ByteArray.emptyWithCapacity (k * n))

/-- Every packed level, level 0 first, from level `z` (`cur`, `2^h` nodes). -/
def levelsGo (hash : Nat → Nat → Vector UInt8 k → Vector UInt8 k → Vector UInt8 k) :
    (h z : Nat) → (cur : ByteArray) → (acc : Array ByteArray) → Array ByteArray
  | 0, _, cur, acc => acc.push cur
  | h + 1, z, cur, acc => levelsGo hash h (z + 1) (parentRow hash z cur (2 ^ h)) (acc.push cur)

/-- Every level of the tree of height `h`, packed, level 0 first: `k * (2^(h+1) - 1)` bytes. -/
def levels (hash : Nat → Nat → Vector UInt8 k → Vector UInt8 k → Vector UInt8 k)
    (leaves : Nat → Vector UInt8 k) (h : Nat) : Array ByteArray :=
  levelsGo hash h 0 (leafRow leaves (2 ^ h)) (Array.mkEmpty (h + 1))

/-- The root, from the packed levels of a tree of height `h`. -/
@[inline] def levelsRoot (lv : Array ByteArray) (h : Nat) : Vector UInt8 k :=
  getD lv[h]! 0

/-- The path of leaf `e`, from the packed levels of a tree of height `h`. -/
@[inline] def levelsPath (lv : Array ByteArray) (h e : Nat) : Vector (Vector UInt8 k) h :=
  Vector.ofFn fun z => getD lv[z.val]! ((e >>> z.val) ^^^ 1)

end EthLib.Cryptography.Merkle.Packed

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants
open EthLib.Cryptography.Merkle.Fast

instance : Inhabited Digest := ⟨Vector.replicate N 0⟩

/-! ## Hypertree trees, pure -/

/-- The node hash of tree `tree` of a layer, at `hashId`. -/
@[inline] def nodeHashPure (pkSeed : PkSeed) (layer : Layer) (tree : Nat) :
    Nat → Nat → Digest → Digest → Digest :=
  fun z j l r => Id.run (nodeHash hashId pkSeed layer tree z j l r)

/-- The leaves of tree `tree` of a layer, at `hashId`. -/
@[inline] def leavesPure (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree : Nat) :
    Nat → Digest :=
  fun e => Id.run (leaves hashId pkSeed prf layer tree e)

/-- Root and path of key `e` of tree `tree` of a layer, every leaf computed once. -/
def treeRootAndPath (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree e : Nat) :
    Digest × Vector Digest layer.height :=
  rootAndPath (nodeHashPure pkSeed layer tree) (leavesPure pkSeed prf layer tree) layer.height e

/-- Every level of tree `tree` of a layer. -/
def treeLevels (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree : Nat) :
    Array (Array Digest) :=
  allLevels (nodeHashPure pkSeed layer tree) (leavesPure pkSeed prf layer tree) layer.height

/-! ## FORS, pure -/

/-- The opening of tree `kappa` at leaf `s` and the tree's root, every leaf computed once. -/
def forsOpenAndRoot (pkSeed : PkSeed) (prf : Prf Id) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) : TreeOpening × Digest :=
  let secret := Id.run (forsSecret prf idx kappa s.val)
  let (root, path) := rootAndPath (fun z j l r => Id.run (forsNodeHash hashId pkSeed idx kappa z j l
      r))
    (fun t => Id.run (forsLeaves hashId pkSeed prf idx kappa t)) FORS_HEIGHT s.val
  ({ secret, path }, root)

/-- `forsSign` and `forsKey` of instance `idx` together: the openings and the FORS public key. -/
def forsSignAndKey (pkSeed : PkSeed) (prf : Prf Id) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    Vector TreeOpening FORS_TREES × Digest :=
  let both := Vector.ofFn fun kappa => forsOpenAndRoot pkSeed prf idx kappa leaves[kappa]
  let openings := both.map Prod.fst
  let roots := both.map Prod.snd
  (openings, Id.run (forsPkFromRoots hashId pkSeed idx roots))

/-! ## Bounded memory

A tree whose leaf is known is built depth first: the specification's own `path`, whose sibling subtrees cover every leaf but the key's, then the climb from that leaf over the path to the root.
Every leaf and node is computed once and at most one node per level is held.

The top tree's leaf is not known when its root is needed, so its levels are kept packed. -/

/-- Root and path of key `e` of tree `tree` of a layer, depth first: the path, then the climb. -/
def treeRootAndPathDF (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree e : Nat) :
    Digest × Vector Digest layer.height :=
  let p := Id.run (path hashId pkSeed prf layer tree e)
  (Id.run (fold hashId pkSeed layer tree e (leavesPure pkSeed prf layer tree e) p), p)

/-- Every level of tree `tree` of a layer, packed at `N` bytes a digest. -/
def treeLevelsPacked (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree : Nat) :
    Array ByteArray :=
  Merkle.Packed.levels (nodeHashPure pkSeed layer tree) (leavesPure pkSeed prf layer tree)
    layer.height

/-- The opening of tree `kappa` at leaf `s` and the tree's root, depth first. The leaf `s` is `F` of the opening's secret, so its `PRF` call is not repeated. -/
def forsOpenAndRootDF (pkSeed : PkSeed) (prf : Prf Id) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) : TreeOpening × Digest :=
  let o := Id.run (treeOpen hashId pkSeed prf idx kappa s)
  let leaf := Id.run (forsLeafHash hashId pkSeed idx kappa s.val o.secret)
  (o, Id.run (Merkle.climb (forsNodeHash hashId pkSeed idx kappa) 0 s.val leaf o.path.toList))

/-- `forsSign` and `forsKey` of instance `idx` together, each tree depth first. -/
def forsSignAndKeyDF (pkSeed : PkSeed) (prf : Prf Id) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    Vector TreeOpening FORS_TREES × Digest :=
  let both := Vector.ofFn fun kappa => forsOpenAndRootDF pkSeed prf idx kappa leaves[kappa]
  let openings := both.map Prod.fst
  let roots := both.map Prod.snd
  (openings, Id.run (forsPkFromRoots hashId pkSeed idx roots))

/-! ## Signing -/

/-- One layer's signature from a path already computed. -/
def signLayerWithPath (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (idx : Nat) (msg : Digest)
    (path : Vector Digest layer.height) : Except SphincsError (LayerSignature layer) :=
  let key := OtsKey.ofIndex layer idx
  match Id.run (otsSign hashId pkSeed prf key msg) with
  | some (counter, chainValues) => .ok { counter, chainValues, path }
  | none => .error (.noAdmissibleEncoding layer)

/-- Everything below the top tree, from the digest and the top key's path. A separate function, not inlined, so that the packed top tree is released before FORS starts. -/
@[noinline] def signBelowTop (pkSeed : PkSeed) (secrets : Prf Id) (rho : Randomizer)
    (d : MessageDigest) (tPath : Vector Digest Layer.top.height) : Except SphincsError Signature :=
  let idx := digestIndex d
  -- FORS: openings and public key, each tree depth first.
  let (fors, bottomMsg) := forsSignAndKeyDF pkSeed secrets idx (digestLeaves d)
  -- Bottom tree: its root is the middle message, its path the bottom signature's.
  let bKey := OtsKey.ofIndex .bottom idx
  let (bRoot, bPath) := treeRootAndPathDF pkSeed secrets .bottom bKey.tree bKey.leaf
  match signLayerWithPath pkSeed secrets .bottom idx bottomMsg bPath with
  | .error err => .error err
  | .ok bottom =>
  let mKey := OtsKey.ofIndex .middle idx
  let (mRoot, mPath) := treeRootAndPathDF pkSeed secrets .middle mKey.tree mKey.leaf
  match signLayerWithPath pkSeed secrets .middle idx bRoot mPath with
  | .error err => .error err
  | .ok middle =>
  match signLayerWithPath pkSeed secrets .top idx mRoot tPath with
  | .error err => .error err
  | .ok top => .ok { randomizer := rho, fors, bottom, middle, top }

/-- `sign`, with every tree built once and bounded memory: the top tree's levels packed (32 KiB), every other tree depth first. -/
def signFast (sk : SecretKey) (msg : Message) : Except SphincsError Signature :=
  let key := Id.run (expandKey hashId sk.seed)
  let pkSeed := key.pkSeed
  let secrets := prf hashId pkSeed sk.seed
  -- The top tree, kept packed: its root is `PK.root`, and its path is needed once `idx` is known.
  let top := treeLevelsPacked pkSeed secrets .top 0
  let pk : PublicKey := { pkSeed, root := Merkle.Packed.levelsRoot top Layer.top.height }
  let rho := Id.run (prfMsg hashId key.skPrf pkSeed msg)
  let d := Id.run (hMsg hashId rho pk.pkSeed pk.root msg)
  let tKey := OtsKey.ofIndex .top (digestIndex d)
  -- The top key's tree is tree 0 for every digest index (`idx < 2^26`); any other tree is built.
  let tPath := if tKey.tree = 0 then Merkle.Packed.levelsPath top Layer.top.height tKey.leaf
    else (treeRootAndPathDF pkSeed secrets .top tKey.tree tKey.leaf).2
  signBelowTop pkSeed secrets rho d tPath

/-- `keyGen` through the level builder. Stock `keyGen` already builds the top tree once, so this is a control: same hash calls, same key, only the data structure differs. -/
def keyGenFast (seed : Seed) : SecretKey × PublicKey :=
  let key := Id.run (expandKey hashId seed)
  let secrets := prf hashId key.pkSeed seed
  let (root, _) := treeRootAndPath key.pkSeed secrets .top 0 0
  (⟨seed⟩, { pkSeed := key.pkSeed, root })

end EthLib.Cryptography.Sphincs
