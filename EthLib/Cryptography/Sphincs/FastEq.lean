module

public import EthLib.Cryptography.Sphincs.Fast

/-!
# The compute-once signer equals the specification

`Fast.lean` builds every Merkle tree of a signature once, level by level.

The specification's `Merkle.path` builds each sibling subtree on its own.

Its `Merkle.root` builds the tree again.

This module proves the two equal in the pure instance:

- `rootAndPath_eq`: one level-by-level pass gives `Merkle.root` and `Merkle.path` of `Id`.
- `allLevels_root`, `allLevels_path`: so do the retained levels of a tree.
- `climb_siblings`: the climb from a leaf over the specification's path reaches the root, so a known-leaf tree needs `Merkle.path` and the climb only.
- `Packed.levels_root`, `Packed.levels_path`: the packed levels give the root and every path.
- `sign_eq_signFast`, `keyGen_eq_keyGenFast`: so do the executable `sign` and `keyGen`.

Only `sign` is installed with `@[csimp]`.

Stock `keyGen` already builds its tree once, and the level builder holds more memory.

`signFast` holds the top tree packed (32,752 bytes) and every other tree depth first.

The equalities hold only in `Id`.

In a query-counting monad, computing a subtree once is not the computation that computes it twice.

So the targets are the concrete constants `sign` and `keyGen`, not `signWith` or `Merkle.path`.

A `@[csimp]` lemma rewrites only code compiled after it is in scope.

So a consumer must import this module, as `Exports/Sphincs.lean` does.
-/

@[expose] public section

open EthLib.Cryptography

namespace EthLib.Cryptography.Merkle.Fast

variable {α : Type} [Inhabited α]

/-- `cur` holds `n` nodes and node `j` of it is `f j`. -/
def IsRow (f : Nat → α) (n : Nat) (cur : Array α) : Prop :=
  cur.size = n ∧ ∀ j < n, cur[j]! = f j

/-- A row of `f` is a row of any `g` that agrees with `f` on its indices. -/
theorem IsRow.congr {f g : Nat → α} {n : Nat} {cur : Array α} (h : IsRow f n cur)
    (hfg : ∀ j < n, f j = g j) : IsRow g n cur :=
  ⟨h.1, fun j hj => (h.2 j hj).trans (hfg j hj)⟩

/-- Reading index `k` after a push. -/
theorem push_get! (acc : Array α) (x : α) (k : Nat) (hk : k < acc.size + 1) :
    (acc.push x)[k]! = if k < acc.size then acc[k]! else x := by
  rw [getElem!_pos (acc.push x) k (by simpa using hk), Array.getElem_push]
  split
  · rename_i h; exact (getElem!_pos acc k h).symm
  · rfl

/-- The leaf loop, from index `i` with the first `i` leaves pushed, gives the leaf row. -/
theorem leafLevelGo_row (leaves : Nat → α) (n i : Nat) (acc : Array α) :
    acc.size = i → i ≤ n → (∀ k < i, acc[k]! = leaves k) →
      IsRow leaves n (leafLevelGo leaves n i acc) := by
  fun_induction leafLevelGo leaves n i acc with
  | case1 i acc hi ih =>
    intro hs _ ha
    apply ih (by simp [hs]) (by omega)
    intro k hk
    rw [push_get! _ _ _ (by omega)]
    split
    · exact ha k (by omega)
    · have : k = i := by omega
      subst this; rfl
  | case2 i acc hi =>
    intro hs hin ha
    have : i = n := by omega
    subst this
    exact ⟨hs, ha⟩

/-- `leafLevel` is the row of the leaves. -/
theorem leafLevel_row (leaves : Nat → α) (n : Nat) : IsRow leaves n (leafLevel leaves n) :=
  leafLevelGo_row leaves n 0 _ (by simp [Array.mkEmpty_eq]) (Nat.zero_le _) (by intro k hk; omega)

/-- The parent loop, from index `j` with the first `j` parents pushed, gives the parent row. -/
theorem parentLevelGo_row (hash : Nat → Nat → α → α → α) (z : Nat) (prev : Array α) (n j : Nat)
    (acc : Array α) :
    acc.size = j → j ≤ n →
      (∀ k < j, acc[k]! = hash (z + 1) k prev[2 * k]! prev[2 * k + 1]!) →
      IsRow (fun k => hash (z + 1) k prev[2 * k]! prev[2 * k + 1]!) n
        (parentLevelGo hash z prev n j acc) := by
  fun_induction parentLevelGo hash z prev n j acc with
  | case1 j acc hj ih =>
    intro hs _ ha
    apply ih (by simp [hs]) (by omega)
    intro k hk
    rw [push_get! _ _ _ (by omega)]
    split
    · exact ha k (by omega)
    · have : k = j := by omega
      subst this; rfl
  | case2 j acc hj =>
    intro hs hin ha
    have : j = n := by omega
    subst this
    exact ⟨hs, ha⟩

section Id

variable (H : Nat → Nat → α → α → Id α) (L : Nat → Id α)

/-- The pure node function of the specification tree. -/
abbrev N (z j : Nat) : α := Id.run (Merkle.node H L z j)

omit [Inhabited α] in
/-- Level 0 holds the leaves. -/
theorem N_zero (j : Nat) : N H L 0 j = Id.run (L j) := rfl

omit [Inhabited α] in
/-- A node is the hash of its two children. -/
theorem N_succ (z j : Nat) :
    N H L (z + 1) j = Id.run (H (z + 1) j (N H L z (2 * j)) (N H L z (2 * j + 1))) := rfl

/-- One level up: the parents of row `z` are row `z + 1`. -/
theorem parentLevel_row (z k : Nat) (cur : Array α) (hc : IsRow (N H L z) (2 ^ (k + 1)) cur) :
    IsRow (N H L (z + 1)) (2 ^ k)
      (parentLevel (fun a b l r => Id.run (H a b l r)) z cur (2 ^ k)) := by
  refine (parentLevelGo_row _ z cur _ 0 _ (by simp [Array.mkEmpty_eq]) (Nat.zero_le _)
    (by intro k hk; omega)).congr ?_
  intro j hj
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [hc.2 (2 * j) (by omega), hc.2 (2 * j + 1) (by omega), N_succ]

omit [Inhabited α] in
/-- One step of `Merkle.siblings`, in `Id`. -/
theorem siblings_succ_id (z j k : Nat) :
    Id.run (Merkle.siblings H L z j (k + 1)) =
      (#v[N H L z (j ^^^ 1)] ++ Id.run (Merkle.siblings H L (z + 1) (j / 2) k)).cast
        (Nat.add_comm 1 k) := rfl

/-- The climb from row `z` of `2^k` nodes reaches node `(z + k, 0)`.

It pushes the siblings `Merkle.siblings` returns, for a leaf whose ancestor at `z` is in the row. -/
theorem climbLevels_spec (e : Nat) : ∀ (k z : Nat) (cur acc : Array α),
    e >>> z < 2 ^ k → IsRow (N H L z) (2 ^ k) cur →
    climbLevels (fun a b l r => Id.run (H a b l r)) e k z cur acc =
      (N H L (z + k) 0, acc ++ (Id.run (Merkle.siblings H L z (e >>> z) k)).toArray)
  | 0, z, cur, acc, _, hc => by
    simp only [climbLevels, Nat.add_zero, hc.2 0 (by simp)]
    rfl
  | k + 1, z, cur, acc, he, hc => by
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hsib : (e >>> z) ^^^ 1 < 2 ^ (k + 1) :=
      Nat.xor_lt_two_pow he (by rw [h2]; have := Nat.one_le_two_pow (n := k); omega)
    have he' : e >>> (z + 1) < 2 ^ k := by rw [Nat.shiftRight_succ]; omega
    rw [climbLevels, climbLevels_spec e k (z + 1) _ _ he' (parentLevel_row H L z k cur hc),
      siblings_succ_id, hc.2 _ hsib, ← Nat.shiftRight_succ]
    simp only [Vector.toArray_cast, Vector.toArray_append, Array.append_assoc,
      Array.push_eq_append]
    refine Prod.ext ?_ ?_
    · show N H L (z + 1 + k) 0 = N H L (z + (k + 1)) 0
      rw [Nat.add_right_comm, Nat.add_assoc]
    · rfl

/-- One level-by-level pass gives the specification's root and path, for a leaf in range. -/
theorem rootAndPath_eq (h e : Nat) (he : e < 2 ^ h) :
    rootAndPath (fun a b l r => Id.run (H a b l r)) (fun i => Id.run (L i)) h e =
      (Id.run (Merkle.root H L h), Id.run (Merkle.path H L h e)) := by
  unfold rootAndPath
  rw [climbLevels_spec H L e h 0 _ _ (by simpa using he)
    ((leafLevel_row (fun i => Id.run (L i)) (2 ^ h)).congr (fun j _ => (N_zero H L j).symm))]
  simp only [Nat.zero_add, Nat.shiftRight_zero, Array.mkEmpty_eq, Array.empty_append]
  refine Prod.ext rfl ?_
  ext i hi
  simp only [Vector.getElem_ofFn]
  rw [getElem!_pos _ i (by simpa using hi)]
  simp [Merkle.path]


/-- A push keeps the old entries. -/
theorem push_get_lt (acc : Array α) (x : α) (k : Nat) (hk : k < acc.size) :
    (acc.push x)[k]! = acc[k]! := by
  rw [push_get! _ _ _ (by omega)]; simp [hk]

/-- A push puts its element at the old size. -/
theorem push_get_size (acc : Array α) (x : α) : (acc.push x)[acc.size]! = x := by
  rw [push_get! _ _ _ (by omega)]; simp

/-- The level loop keeps the levels already pushed. -/
theorem allLevelsGo_prefix (hash : Nat → Nat → α → α → α) :
    ∀ (k z : Nat) (cur : Array α) (acc : Array (Array α)) (i : Nat), i < acc.size →
      (allLevelsGo hash k z cur acc)[i]! = acc[i]!
  | 0, _, _, _, i, hi => by rw [allLevelsGo, push_get_lt _ _ _ hi]
  | k + 1, z, cur, acc, i, hi => by
    rw [allLevelsGo, allLevelsGo_prefix hash k _ _ _ i (by simp; omega), push_get_lt _ _ _ hi]

/-- Entry `acc.size + i` of the level loop from row `z` is row `z + i`. -/
theorem allLevelsGo_row : ∀ (k z : Nat) (cur : Array α) (acc : Array (Array α)),
    IsRow (N H L z) (2 ^ k) cur → ∀ i ≤ k,
      IsRow (N H L (z + i)) (2 ^ (k - i))
        (allLevelsGo (fun a b l r => Id.run (H a b l r)) k z cur acc)[acc.size + i]!
  | 0, z, cur, acc, hc, i, hi => by
    obtain rfl : i = 0 := by omega
    simp only [allLevelsGo, Nat.add_zero]; rw [push_get_size]; simpa using hc
  | k + 1, z, cur, acc, hc, i, hi => by
    rw [allLevelsGo]
    cases i with
    | zero =>
      simp only [Nat.add_zero]; rw [allLevelsGo_prefix _ _ _ _ _ _ (by simp), push_get_size]
      simpa using hc
    | succ i =>
      have := allLevelsGo_row k (z + 1) _ (acc.push cur) (parentLevel_row H L z k cur hc) i
        (by omega)
      rw [Array.size_push] at this
      have e1 : acc.size + 1 + i = acc.size + (i + 1) := by omega
      have e2 : z + 1 + i = z + (i + 1) := by omega
      have e3 : k - i = k + 1 - (i + 1) := by omega
      rw [e1, e2, e3] at this
      exact this

/-- Entry `i` of `allLevels` is row `i` of the tree. -/
theorem allLevels_row (h i : Nat) (hi : i ≤ h) :
    IsRow (N H L i) (2 ^ (h - i))
      (allLevels (fun a b l r => Id.run (H a b l r)) (fun j => Id.run (L j)) h)[i]! := by
  have := allLevelsGo_row H L h 0 _ (Array.mkEmpty (h + 1))
    ((leafLevel_row (fun j => Id.run (L j)) (2 ^ h)).congr (fun j _ => (N_zero H L j).symm)) i hi
  simpa [allLevels, Array.mkEmpty_eq] using this

/-- The retained levels give the specification's root. -/
theorem allLevels_root (h : Nat) :
    levelsRoot (allLevels (fun a b l r => Id.run (H a b l r)) (fun j => Id.run (L j)) h) h =
      Id.run (Merkle.root H L h) := by
  have := (allLevels_row H L h h (Nat.le_refl h)).2 0 (by simp)
  exact this

omit [Inhabited α] in
/-- Entry `i` of `Merkle.siblings` from `(z, j)` is the sibling of the ancestor at `z + i`. -/
theorem siblings_get : ∀ (n z j i : Nat) (hi : i < n),
    (Id.run (Merkle.siblings H L z j n))[i] = N H L (z + i) ((j >>> i) ^^^ 1)
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, z, j, i, hi => by
    rw [siblings_succ_id]
    cases i with
    | zero => simp
    | succ i =>
      have := siblings_get n (z + 1) (j / 2) i (by omega)
      have hs : j >>> (i + 1) = (j / 2) >>> i := by
        rw [Nat.shiftRight_succ, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
          Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
      have hz : z + (i + 1) = z + 1 + i := by omega
      rw [Vector.getElem_cast, Vector.getElem_append_right]
      · simp only [Nat.add_sub_cancel, hs, hz]; exact this
      · omega

omit [Inhabited α] in
/-- The sibling index at level `i` of a leaf below `2^h` is in its row. -/
theorem shift_xor_lt (h e i : Nat) (he : e < 2 ^ h) (hi : i < h) :
    (e >>> i) ^^^ 1 < 2 ^ (h - i) := by
  apply Nat.xor_lt_two_pow
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos i), ← Nat.pow_add,
      Nat.sub_add_cancel (Nat.le_of_lt hi)]
    exact he
  · exact Nat.one_lt_two_pow (by omega)

/-- The retained levels give the specification's path, for a leaf in range. -/
theorem allLevels_path (h e : Nat) (he : e < 2 ^ h) :
    levelsPath (allLevels (fun a b l r => Id.run (H a b l r)) (fun j => Id.run (L j)) h) h e =
      Id.run (Merkle.path H L h e) := by
  ext i hi
  simp only [levelsPath, Vector.getElem_ofFn]
  rw [(allLevels_row H L h i (Nat.le_of_lt hi)).2 _ (shift_xor_lt h e i he hi)]
  unfold Merkle.path
  rw [siblings_get H L h 0 e i hi, Nat.zero_add]

omit [Inhabited α] in
/-- Flipping the low bit: up one if even, down one if odd. -/
theorem xor_one_eq (j : Nat) : j ^^^ 1 = if j % 2 = 0 then j + 1 else j - 1 := by
  have h1 : (j ^^^ 1) / 2 = j / 2 := by rw [Nat.xor_div_two]; simp
  have h2 : (j ^^^ 1) % 2 = 1 ↔ ¬ (j % 2 = 1 ↔ 1 % 2 = 1) := Nat.xor_mod_two_eq_one
  have h3 := Nat.div_add_mod (j ^^^ 1) 2
  have h4 := Nat.div_add_mod j 2
  have h5 := Nat.mod_lt (j ^^^ 1) (by decide : 2 > 0)
  have h6 := Nat.mod_lt j (by decide : 2 > 0)
  split
  · have : (j ^^^ 1) % 2 = 1 := h2.2 (by omega)
    omega
  · have : ¬ (j ^^^ 1) % 2 = 1 := fun h => (h2.1 h) (by omega)
    omega

omit [Inhabited α] in
/-- A node and its sibling, in the order `Merkle.ordered` puts them, hash to the parent. -/
theorem ordered_parent (z j : Nat) :
    Id.run (H (z + 1) (j / 2) (Merkle.ordered j (N H L z j) (N H L z (j ^^^ 1))).1
      (Merkle.ordered j (N H L z j) (N H L z (j ^^^ 1))).2) = N H L (z + 1) (j / 2) := by
  rw [N_succ, xor_one_eq]
  unfold Merkle.ordered
  by_cases hj : j % 2 = 0
  · have e1 : 2 * (j / 2) = j := by omega
    simp only [hj, ite_true, e1]
  · have e1 : 2 * (j / 2) = j - 1 := by omega
    have e2 : 2 * (j / 2) + 1 = j := by omega
    simp only [hj, ite_false]
    rw [e2, e1]

omit [Inhabited α] in
/-- Climbing from node `(z, j)` over the siblings `Merkle.siblings` returns reaches the ancestor `k` levels up. So the climb from a leaf over its path reaches the root. -/
theorem climb_siblings : ∀ (k z j : Nat),
    Id.run (Merkle.climb H z j (N H L z j) (Id.run (Merkle.siblings H L z j k)).toList) =
      N H L (z + k) (j >>> k)
  | 0, z, j => by simp [Merkle.siblings, Merkle.climb]
  | k + 1, z, j => by
    rw [siblings_succ_id]
    simp only [Vector.toList_cast, Vector.toList_append]
    show Id.run (Merkle.climb H (z + 1) (j / 2)
      (Id.run (H (z + 1) (j / 2) (Merkle.ordered j (N H L z j) (N H L z (j ^^^ 1))).1
        (Merkle.ordered j (N H L z j) (N H L z (j ^^^ 1))).2))
      (Id.run (Merkle.siblings H L (z + 1) (j / 2) k)).toList) = _
    rw [ordered_parent, climb_siblings k (z + 1) (j / 2)]
    have hs : j >>> (k + 1) = (j / 2) >>> k := by
      rw [Nat.shiftRight_succ, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
        Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [hs, Nat.add_right_comm, Nat.add_assoc]

end Id

end EthLib.Cryptography.Merkle.Fast

namespace EthLib.Cryptography.Merkle.Packed

open EthLib.Cryptography.Merkle.Fast (N N_zero N_succ siblings_get shift_xor_lt)

variable {k : Nat}

/-- `pushGo` appends the bytes of `d` from index `i`. -/
theorem pushGo_toList (buf : ByteArray) (d : Vector UInt8 k) (i : Nat) (hi : i ≤ k) :
    (pushGo buf d i).data.toList = buf.data.toList ++ d.toList.drop i := by
  fun_induction pushGo buf d i with
  | case1 buf i h ih =>
    rw [ih (by omega), ByteArray.data_push, Array.toList_push, List.append_assoc]
    congr 1
    have e := List.drop_eq_getElem_cons (l := d.toList) (i := i) (by simpa using h)
    rw [e]; simp
  | case2 buf i h =>
    have : i = k := by omega
    subst this; simp

/-- `pushD` appends the bytes of `d`. -/
theorem pushD_data (buf : ByteArray) (d : Vector UInt8 k) :
    (pushD buf d).data = buf.data ++ d.toArray := by
  apply Array.toList_inj.mp
  rw [pushD, pushGo_toList _ _ _ (Nat.zero_le _)]; simp; rfl

theorem pushD_size (buf : ByteArray) (d : Vector UInt8 k) :
    (pushD buf d).size = buf.size + k := by
  show (pushD buf d).data.size = buf.data.size + k
  rw [pushD_data]; simp

/-- A push keeps the digests already packed. -/
theorem getD_pushD_old (buf : ByteArray) (d : Vector UInt8 k) (j : Nat)
    (hj : k * (j + 1) ≤ buf.size) : getD (pushD buf d) j = (getD buf j : Vector UInt8 k) := by
  ext i hi
  simp only [getD, Vector.getElem_ofFn]
  show (pushD buf d).data[k * j + i]! = buf.data[k * j + i]!
  have hs : buf.size = buf.data.size := rfl
  have hb : k * j + i < buf.data.size := by
    rw [Nat.mul_add, Nat.mul_one] at hj; omega
  have h1 : k * j + i < (buf.data ++ d.toArray).size := by simp; omega
  rw [pushD_data, getElem!_pos (buf.data ++ d.toArray) (k * j + i) h1,
    getElem!_pos buf.data (k * j + i) hb, Array.getElem_append_left hb]

/-- A push puts its digest at the next index. -/
theorem getD_pushD_new (buf : ByteArray) (d : Vector UInt8 k) (j : Nat)
    (hj : buf.size = k * j) : getD (pushD buf d) j = d := by
  ext i hi
  simp only [getD, Vector.getElem_ofFn]
  show (pushD buf d).data[k * j + i]! = d[i]
  have hs : buf.size = buf.data.size := rfl
  have h1 : k * j + i < (buf.data ++ d.toArray).size := by simp; omega
  rw [pushD_data, getElem!_pos (buf.data ++ d.toArray) (k * j + i) h1,
    Array.getElem_append_right (by omega)]
  simp [← hs, hj]

/-- `buf` packs `n` digests and digest `j` of it is `f j`. -/
def IsPRow (f : Nat → Vector UInt8 k) (n : Nat) (buf : ByteArray) : Prop :=
  buf.size = k * n ∧ ∀ j < n, getD buf j = f j

theorem IsPRow.congr {f g : Nat → Vector UInt8 k} {n : Nat} {buf : ByteArray}
    (h : IsPRow f n buf) (hfg : ∀ j < n, f j = g j) : IsPRow g n buf :=
  ⟨h.1, fun j hj => (h.2 j hj).trans (hfg j hj)⟩

/-- One packed push extends a packed prefix. -/
theorem push_prefix (f : Nat → Vector UInt8 k) (i : Nat) (acc : ByteArray)
    (hs : acc.size = k * i) (ha : ∀ j < i, getD acc j = f j) :
    (pushD acc (f i)).size = k * (i + 1) ∧ ∀ j < i + 1, getD (pushD acc (f i)) j = f j := by
  refine ⟨by rw [pushD_size, hs, Nat.mul_add, Nat.mul_one], fun j hj => ?_⟩
  by_cases hji : j < i
  · rw [getD_pushD_old _ _ _ (by rw [hs]; exact Nat.mul_le_mul_left _ hji)]; exact ha j hji
  · have : j = i := by omega
    subst this; exact getD_pushD_new _ _ _ hs

theorem emptyWithCapacity_size (c : Nat) : (ByteArray.emptyWithCapacity c).size = 0 := rfl

theorem leafRowGo_row (leaves : Nat → Vector UInt8 k) (n i : Nat) (acc : ByteArray) :
    acc.size = k * i → i ≤ n → (∀ j < i, getD acc j = leaves j) →
      IsPRow leaves n (leafRowGo leaves n i acc) := by
  fun_induction leafRowGo leaves n i acc with
  | case1 i acc hi ih =>
    intro hs _ ha
    have := push_prefix leaves i acc hs ha
    exact ih this.1 (by omega) this.2
  | case2 i acc hi =>
    intro hs hin ha
    have : i = n := by omega
    subst this
    exact ⟨hs, ha⟩

theorem leafRow_row (leaves : Nat → Vector UInt8 k) (n : Nat) :
    IsPRow leaves n (leafRow leaves n) :=
  leafRowGo_row leaves n 0 _ (by rw [emptyWithCapacity_size]; simp) (Nat.zero_le _)
    (by intro j hj; omega)

theorem parentRowGo_row (hash : Nat → Nat → Vector UInt8 k → Vector UInt8 k → Vector UInt8 k)
    (z : Nat) (prev : ByteArray) (n j : Nat) (acc : ByteArray) :
    acc.size = k * j → j ≤ n →
      (∀ i < j, getD acc i = hash (z + 1) i (getD prev (2 * i)) (getD prev (2 * i + 1))) →
      IsPRow (fun i => hash (z + 1) i (getD prev (2 * i)) (getD prev (2 * i + 1))) n
        (parentRowGo hash z prev n j acc) := by
  fun_induction parentRowGo hash z prev n j acc with
  | case1 j acc hj ih =>
    intro hs _ ha
    have := push_prefix (fun i => hash (z + 1) i (getD prev (2 * i)) (getD prev (2 * i + 1)))
      j acc hs ha
    exact ih this.1 (by omega) this.2
  | case2 j acc hj =>
    intro hs hin ha
    have : j = n := by omega
    subst this
    exact ⟨hs, ha⟩

section Id

variable (H : Nat → Nat → Vector UInt8 k → Vector UInt8 k → Id (Vector UInt8 k))
  (L : Nat → Id (Vector UInt8 k))

/-- One level up: the parents of packed row `z` are packed row `z + 1`. -/
theorem parentRow_row (z h : Nat) (cur : ByteArray) (hc : IsPRow (N H L z) (2 ^ (h + 1)) cur) :
    IsPRow (N H L (z + 1)) (2 ^ h)
      (parentRow (fun a b l r => Id.run (H a b l r)) z cur (2 ^ h)) := by
  refine (parentRowGo_row _ z cur _ 0 _ (by rw [emptyWithCapacity_size]; simp) (Nat.zero_le _)
    (by intro i hi; omega)).congr ?_
  intro j hj
  have h2 : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ]; omega
  show Id.run (H (z + 1) j (getD cur (2 * j)) (getD cur (2 * j + 1))) = N H L (z + 1) j
  rw [hc.2 (2 * j) (by omega), hc.2 (2 * j + 1) (by omega), N_succ]

/-- A push keeps the old entries. -/
theorem push_get_lt (acc : Array ByteArray) (x : ByteArray) (i : Nat) (hi : i < acc.size) :
    (acc.push x)[i]! = acc[i]! :=
  EthLib.Cryptography.Merkle.Fast.push_get_lt acc x i hi

theorem push_get_size (acc : Array ByteArray) (x : ByteArray) : (acc.push x)[acc.size]! = x :=
  EthLib.Cryptography.Merkle.Fast.push_get_size acc x

/-- The level loop keeps the levels already pushed. -/
theorem levelsGo_prefix (hash : Nat → Nat → Vector UInt8 k → Vector UInt8 k → Vector UInt8 k) :
    ∀ (h z : Nat) (cur : ByteArray) (acc : Array ByteArray) (i : Nat), i < acc.size →
      (levelsGo hash h z cur acc)[i]! = acc[i]!
  | 0, _, _, _, i, hi => by rw [levelsGo, push_get_lt _ _ _ hi]
  | h + 1, z, cur, acc, i, hi => by
    rw [levelsGo, levelsGo_prefix hash h _ _ _ i (by simp; omega), push_get_lt _ _ _ hi]

/-- Entry `acc.size + i` of the level loop from packed row `z` is packed row `z + i`. -/
theorem levelsGo_row : ∀ (h z : Nat) (cur : ByteArray) (acc : Array ByteArray),
    IsPRow (N H L z) (2 ^ h) cur → ∀ i ≤ h,
      IsPRow (N H L (z + i)) (2 ^ (h - i))
        (levelsGo (fun a b l r => Id.run (H a b l r)) h z cur acc)[acc.size + i]!
  | 0, z, cur, acc, hc, i, hi => by
    obtain rfl : i = 0 := by omega
    simp only [levelsGo, Nat.add_zero]; rw [push_get_size]; simpa using hc
  | h + 1, z, cur, acc, hc, i, hi => by
    rw [levelsGo]
    cases i with
    | zero =>
      simp only [Nat.add_zero]; rw [levelsGo_prefix _ _ _ _ _ _ (by simp), push_get_size]
      simpa using hc
    | succ i =>
      have := levelsGo_row h (z + 1) _ (acc.push cur) (parentRow_row H L z h cur hc) i
        (by omega)
      rw [Array.size_push] at this
      have e1 : acc.size + 1 + i = acc.size + (i + 1) := by omega
      have e2 : z + 1 + i = z + (i + 1) := by omega
      have e3 : h - i = h + 1 - (i + 1) := by omega
      rw [e1, e2, e3] at this
      exact this

/-- Entry `i` of `levels` is packed row `i` of the tree. -/
theorem levels_row (h i : Nat) (hi : i ≤ h) :
    IsPRow (N H L i) (2 ^ (h - i))
      (levels (fun a b l r => Id.run (H a b l r)) (fun j => Id.run (L j)) h)[i]! := by
  have := levelsGo_row H L h 0 _ (Array.mkEmpty (h + 1))
    ((leafRow_row (fun j => Id.run (L j)) (2 ^ h)).congr (fun j _ => (N_zero H L j).symm)) i hi
  simpa [levels, Array.mkEmpty_eq] using this

/-- The packed levels give the specification's root. -/
theorem levels_root (h : Nat) :
    levelsRoot (levels (fun a b l r => Id.run (H a b l r)) (fun j => Id.run (L j)) h) h =
      Id.run (Merkle.root H L h) :=
  (levels_row H L h h (Nat.le_refl h)).2 0 (by simp)

/-- The packed levels give the specification's path, for a leaf in range. -/
theorem levels_path (h e : Nat) (he : e < 2 ^ h) :
    levelsPath (levels (fun a b l r => Id.run (H a b l r)) (fun j => Id.run (L j)) h) h e =
      Id.run (Merkle.path H L h e) := by
  apply Vector.ext
  intro i hi
  simp only [levelsPath, Vector.getElem_ofFn]
  rw [(levels_row H L h i (Nat.le_of_lt hi)).2 _ (shift_xor_lt h e i he hi)]
  unfold Merkle.path
  rw [siblings_get H L h 0 e i hi, Nat.zero_add]

end Id

end EthLib.Cryptography.Merkle.Packed

namespace EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants EthLib.Cryptography.Merkle.Fast

/-- `ofFnInOrder` in `Id` is `Vector.ofFn`. -/
theorem ofFnInOrder_id {β : Type} : ∀ (n : Nat) (f : Fin n → Id β),
    Id.run (HashSig.ofFnInOrder (m := Id) n f) = Vector.ofFn fun i => Id.run (f i)
  | 0, f => by ext i hi; exact absurd hi (Nat.not_lt_zero _)
  | n + 1, f => by
    show (#v[Id.run (f 0)] ++ Id.run (HashSig.ofFnInOrder (m := Id) n fun i => f i.succ)).cast
      (Nat.add_comm 1 n) = _
    rw [ofFnInOrder_id n]
    ext i hi
    cases i with
    | zero => simp
    | succ i =>
      rw [Vector.getElem_cast, Vector.getElem_append_right]
      · simp only [Nat.add_sub_cancel, Vector.getElem_ofFn]
        rfl
      · omega

/-- `treeRootAndPath` is `treeRoot` and `path` at `hashId`, for a key in range. -/
theorem treeRootAndPath_eq (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree e : Nat)
    (he : e < 2 ^ layer.height) :
    treeRootAndPath pkSeed prf layer tree e =
      (Id.run (treeRoot hashId pkSeed prf layer tree),
       Id.run (path hashId pkSeed prf layer tree e)) :=
  rootAndPath_eq (nodeHash hashId pkSeed layer tree) (leaves hashId pkSeed prf layer tree) _ _ he

/-- The retained levels of a hypertree tree give `treeRoot`. -/
theorem treeLevels_root (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree : Nat) :
    levelsRoot (treeLevels pkSeed prf layer tree) layer.height =
      Id.run (treeRoot hashId pkSeed prf layer tree) :=
  allLevels_root (nodeHash hashId pkSeed layer tree) (leaves hashId pkSeed prf layer tree) _

/-- The retained levels of a hypertree tree give `path`, for a key in range. -/
theorem treeLevels_path (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree e : Nat)
    (he : e < 2 ^ layer.height) :
    levelsPath (treeLevels pkSeed prf layer tree) layer.height e =
      Id.run (path hashId pkSeed prf layer tree e) :=
  allLevels_path (nodeHash hashId pkSeed layer tree) (leaves hashId pkSeed prf layer tree) _ _ he

/-- The leaf of a layer's key is below `2^h` for the layer's height `h`. -/
theorem ofIndex_leaf_lt (layer : Layer) (idx : Nat) :
    (OtsKey.ofIndex layer idx).leaf < 2 ^ layer.height :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- One FORS tree, built once, gives `treeOpen` and `forsRoot`. -/
theorem forsOpenAndRoot_eq (pkSeed : PkSeed) (prf : Prf Id) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) :
    forsOpenAndRoot pkSeed prf idx kappa s =
      (Id.run (treeOpen hashId pkSeed prf idx kappa s),
       Id.run (forsRoot hashId pkSeed prf idx kappa)) := by
  unfold forsOpenAndRoot
  rw [rootAndPath_eq (forsNodeHash hashId pkSeed idx kappa) (forsLeaves hashId pkSeed prf idx kappa)
    _ _ s.isLt]
  rfl

/-- `forsSignAndKey` is `forsSign` and `forsKey` at `hashId`. -/
theorem forsSignAndKey_eq (pkSeed : PkSeed) (prf : Prf Id) (idx : Nat)
    (ls : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    forsSignAndKey pkSeed prf idx ls =
      (Id.run (forsSign hashId pkSeed prf idx ls), Id.run (forsKey hashId pkSeed prf idx)) := by
  unfold forsSignAndKey forsSign forsKey
  simp only [forsOpenAndRoot_eq, Vector.map_ofFn, Id.run_bind, ofFnInOrder_id]
  rfl

/-- A layer signature from the key's specification path is `signLayer`. -/
theorem signLayerWithPath_eq (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (idx : Nat)
    (msg : Digest) :
    signLayerWithPath pkSeed prf layer idx msg
        (Id.run (path hashId pkSeed prf layer (OtsKey.ofIndex layer idx).tree
          (OtsKey.ofIndex layer idx).leaf)) =
      Id.run (signLayer hashId pkSeed prf layer idx msg) := by
  unfold signLayerWithPath signLayer
  dsimp only
  cases h : otsSign hashId pkSeed prf (OtsKey.ofIndex layer idx) msg with
  | none => rfl
  | some p => obtain ⟨c, cv⟩ := p; rfl

/-- Depth first, a hypertree tree gives `treeRoot` and `path`, for a key in range. -/
theorem treeRootAndPathDF_eq (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree e : Nat)
    (he : e < 2 ^ layer.height) :
    treeRootAndPathDF pkSeed prf layer tree e =
      (Id.run (treeRoot hashId pkSeed prf layer tree),
       Id.run (path hashId pkSeed prf layer tree e)) := by
  refine Prod.ext ?_ rfl
  show Id.run (Merkle.climb (nodeHash hashId pkSeed layer tree) 0 e
    (N (nodeHash hashId pkSeed layer tree) (leaves hashId pkSeed prf layer tree) 0 e)
    (Id.run (Merkle.siblings (nodeHash hashId pkSeed layer tree)
      (leaves hashId pkSeed prf layer tree) 0 e layer.height)).toList) = _
  rw [climb_siblings, Nat.zero_add, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt he]
  rfl

/-- The packed levels of a hypertree tree give `treeRoot`. -/
theorem treeLevelsPacked_root (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree : Nat) :
    Merkle.Packed.levelsRoot (treeLevelsPacked pkSeed prf layer tree) layer.height =
      Id.run (treeRoot hashId pkSeed prf layer tree) :=
  Merkle.Packed.levels_root (nodeHash hashId pkSeed layer tree)
    (leaves hashId pkSeed prf layer tree) _

/-- The packed levels of a hypertree tree give `path`, for a key in range. -/
theorem treeLevelsPacked_path (pkSeed : PkSeed) (prf : Prf Id) (layer : Layer) (tree e : Nat)
    (he : e < 2 ^ layer.height) :
    Merkle.Packed.levelsPath (treeLevelsPacked pkSeed prf layer tree) layer.height e =
      Id.run (path hashId pkSeed prf layer tree e) :=
  Merkle.Packed.levels_path (nodeHash hashId pkSeed layer tree)
    (leaves hashId pkSeed prf layer tree) _ _ he

/-- One FORS tree, depth first, gives `treeOpen` and `forsRoot`. -/
theorem forsOpenAndRootDF_eq (pkSeed : PkSeed) (prf : Prf Id) (idx : Nat)
    (kappa : Fin FORS_TREES) (s : Fin (2 ^ FORS_HEIGHT)) :
    forsOpenAndRootDF pkSeed prf idx kappa s =
      (Id.run (treeOpen hashId pkSeed prf idx kappa s),
       Id.run (forsRoot hashId pkSeed prf idx kappa)) := by
  refine Prod.ext rfl ?_
  simp only [forsOpenAndRootDF, treeOpen, Id.run_bind, Id.run_pure]
  -- The leaf from the opening's secret is the specification's leaf `s`.
  have hl : Id.run (forsLeafHash hashId pkSeed idx kappa s.val
      (Id.run (forsSecret prf idx kappa s.val))) =
      N (forsNodeHash hashId pkSeed idx kappa) (forsLeaves hashId pkSeed prf idx kappa) 0 s.val :=
    rfl
  have h := climb_siblings (forsNodeHash hashId pkSeed idx kappa)
    (forsLeaves hashId pkSeed prf idx kappa) FORS_HEIGHT 0 s.val
  rw [Nat.zero_add, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt s.isLt] at h
  rw [hl]
  unfold Merkle.path forsRoot Merkle.root
  exact h

/-- `forsSignAndKeyDF` is `forsSign` and `forsKey` at `hashId`. -/
theorem forsSignAndKeyDF_eq (pkSeed : PkSeed) (prf : Prf Id) (idx : Nat)
    (ls : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    forsSignAndKeyDF pkSeed prf idx ls =
      (Id.run (forsSign hashId pkSeed prf idx ls), Id.run (forsKey hashId pkSeed prf idx)) := by
  unfold forsSignAndKeyDF forsSign forsKey
  simp only [forsOpenAndRootDF_eq, Vector.map_ofFn, Id.run_bind, ofFnInOrder_id]
  rfl

/-- Both branches of the top path in `signFast` give the specification's path. -/
theorem topPathDF_eq (pkSeed : PkSeed) (prf : Prf Id) (k : OtsKey)
    (hk : k.leaf < 2 ^ Layer.top.height) :
    (if k.tree = 0 then
        Merkle.Packed.levelsPath (treeLevelsPacked pkSeed prf .top 0) Layer.top.height k.leaf
      else (treeRootAndPathDF pkSeed prf .top k.tree k.leaf).2) =
      Id.run (path hashId pkSeed prf .top k.tree k.leaf) := by
  split
  · rename_i h; rw [h]; exact treeLevelsPacked_path _ _ _ _ _ hk
  · rw [treeRootAndPathDF_eq _ _ _ _ _ hk]

/-- Compiled code that calls `sign` runs `signFast`; the kernel still reasons about `sign`. -/
@[csimp] theorem sign_eq_signFast : @sign = @signFast := by
  funext sk msg
  unfold signFast signBelowTop
  dsimp only
  simp only [topPathDF_eq _ _ _ (ofIndex_leaf_lt _ _)]
  simp only [treeLevelsPacked_root, forsSignAndKeyDF_eq,
    treeRootAndPathDF_eq _ _ _ _ _ (ofIndex_leaf_lt _ _), signLayerWithPath_eq]
  simp only [sign, signWith, signDerived, publicKeyOf, layerMessage, Id.run_bind, Id.run_pure]
  generalize (signLayer hashId _ _ Layer.bottom _ _).run = rb
  cases rb with
  | error err => rfl
  | ok bottom =>
    simp only [Id.run_bind, Id.run_pure]
    generalize (signLayer hashId _ _ Layer.middle _ _).run = rm
    cases rm with
    | error err => rfl
    | ok middle =>
      simp only [Id.run_bind, Id.run_pure]
      generalize (signLayer hashId _ _ Layer.top _ _).run = rt
      cases rt with
      | error err => rfl
      | ok top => rfl

/-- `keyGen` equals `keyGenFast`.

It is not installed with `@[csimp]`: both evaluate 264,193 hashes, and `keyGenFast` holds more. -/
theorem keyGen_eq_keyGenFast : @keyGen = @keyGenFast := by
  funext seed
  unfold keyGenFast
  dsimp only
  rw [treeRootAndPath_eq _ _ _ _ _ (Nat.two_pow_pos _)]
  simp only [keyGen, keyGenWith, publicKeyOf, Id.run_bind, Id.run_pure]

end EthLib.Cryptography.Sphincs
