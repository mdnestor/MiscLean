
/-

Binary trees

-/

variable {X Y: Type}

-- A tree is grown inductively given an element x ∈ X and (optionally) left/right children.

inductive Tree (X: Type) where
| empty: Tree X
| grow (x: X) (L R: Tree X): Tree X

namespace Tree

-- Given an element x, returns the tree with a single node and no children.

def leaf (x: X): Tree X :=
  grow x empty empty

-- Tells whether an element appears somewhere in a tree.

def contains (T: Tree X) (x₀: X): Prop :=
  match T with
  | empty => False
  | grow x L R => x = x₀ ∨ (contains L x₀) ∨ (contains R x₀)

-- The leaf of x contains x.

def contains_leaf (x: X): contains (leaf x) x := by
  apply Or.inl
  rfl

-- Inversion of a tree.

def invert (T: Tree X): Tree X :=
  match T with
  | empty => empty
  | grow x L R => grow x (invert R) (invert L)

-- Inversion is idempotent.

theorem invert_invert (T: Tree X): invert (invert T) = T := by
  induction T with
  | empty => rfl
  | grow x L R hL hR => calc
    (grow x L R).invert.invert
    _ = (grow x R.invert L.invert).invert := by rfl
    _ = grow x L.invert.invert R.invert.invert := by rfl
    _ = grow x L R := by rw [hL, hR]

-- The height of a tree.

def height (T: Tree X): Nat :=
  match T with
  | empty => 0
  | grow _ L R => max (height L) (height R) + 1

-- The height of a leaf is one.

theorem height_leaf (x: X): height (leaf x) = 1 := by
  rfl

-- Inversion preserves height.

theorem height_invert (T: Tree X): height (invert T) = height T := by
  induction T with
  | empty => rfl
  | grow x L R hL hR => calc
    (grow x L R).invert.height
    _ = (grow x R.invert L.invert).height := rfl
    _ = max R.invert.height L.invert.height + 1 := rfl
    _ = max R.height L.height + 1 := by rw [hL, hR]
    _ = max L.height R.height + 1 := by rw [Nat.max_comm]
    _ = (grow x L R).height := rfl

-- The size of a tree is the total number of nodes.

def size (T: Tree X): Nat :=
  match T with
  | empty => 0
  | grow _ L R => (size L + size R) + 1

-- Inversion preserves size.

theorem size_invert (T: Tree X): size (invert T) = size T := by
  induction T with
  | empty => rfl
  | grow x L R hL hR => calc
    (grow x L R).invert.size
    _ = (grow x R.invert L.invert).size := by rfl
    _ = (R.invert.size + L.invert.size) + 1 := by rfl
    _ = (R.size + L.size) + 1 := by rw [hL, hR]
    _ = (L.size + R.size) + 1 := by rw [Nat.add_comm L.size R.size]
    _ = (grow x L R).size := by rfl

-- Theorem: a tree of depth d has size at most 1 + 2 + 4 + ... + 2^d.

-- This requires some facts about the geometric sum.

-- geom(r, n) = 1 + r + r^2 + ... + r^(n - 1).

def geom (r: Nat) (n: Nat): Nat :=
  match n with
  | 0 => 0
  | p + 1 => geom r p + r^p

theorem geom_mono (r: Nat) (m n: Nat) (h: m ≤ n): geom r m ≤ geom r n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem geom_mul (r: Nat) (n: Nat): r * geom r n + 1 = geom r (n + 1) := by
  induction n with
  | zero => rfl
  | succ p hp => calc
    r * geom r (p + 1) + 1
    _ = r * (geom r p + r^p) + 1 := by rfl
    _ = r * geom r p + r * r^p + 1 := by rw [Nat.mul_add]
    _ = (r * geom r p + 1) + r * r^p := by apply Nat.add_right_comm
    _ = geom r (p + 1) + r * r^p := by exact Nat.add_left_inj.mpr hp
    _ = geom r (p + 1) + r^(p + 1) := by rw [Nat.pow_succ']
    _ = geom r (p + 1 + 1) := by rfl

-- Now we can prove the theorem.

theorem geometric_size_bound (T: Tree X): size T ≤ geom 2 (height T) := by
  induction T with
  | empty => apply Nat.zero_le
  | grow x L R hL hR => calc
    (grow x L R).size
    _ = (size L + size R) + 1 := by rfl
    _ ≤ (geom 2 L.height + geom 2 R.height) + 1 := by
      exact Nat.add_le_add_right (Nat.add_le_add hL hR) 1
    _ ≤ (geom 2 (max L.height R.height) + geom 2 (max L.height R.height)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.add_le_add
      · exact geom_mono 2 L.height (max L.height R.height) (Nat.le_max_left _ _)
      · exact geom_mono 2 R.height (max L.height R.height) (Nat.le_max_right _ _)
    _ = 2 * geom 2 (max L.height R.height) + 1 := by rw [Nat.two_mul]
    _ = geom 2 (max L.height R.height + 1) := by rw [geom_mul]
    _ = geom 2 (grow x L R).height := by rfl

-- Given a list of bools, attempt to climb the tree (with false ↦ left, true ↦ right).
-- Returns the list of all elements encountered (and possibly stopping early).

def climb (T: Tree X) (B: List Bool): List X :=
  match T with
  | empty => []
  | grow x L R => List.cons x (
    match B with
    | List.nil => []
    | List.cons b B' => match b with
      | true => climb L B'
      | false => climb R B'
  )

-- Theorem: climbing an inverted tree with a negated list yields the same result.

theorem climb_invert (T: Tree X) (B: List Bool): climb (invert T) (List.map not B) = climb T B := by
  induction T generalizing B with
  | empty => rfl
  | grow x L R hL hR =>
    cases B with
    | nil => rfl
    | cons b B' =>
      cases b <;> simp [climb, invert, hL, hR]

-- Given a tree T and an element x, insert a new node as the left child of T,
-- such that x adopts the previous left child (and empty right child).

def insert_left (T: Tree X) (x: X): Tree X :=
  match T with
  | empty => grow x empty empty
  | grow x₀ L R => grow x₀ (grow x L empty) R

def insert_right (T: Tree X) (x: X): Tree X :=
  invert (insert_left (invert T) x)

-- Depth first search

-- Depth-first pre-order search
def search_dfpr (T: Tree X): List X :=
  match T with
  | empty => []
  | grow x L R => [x] ++ search_dfpr L ++ search_dfpr R

-- Depth-first in-order
def search_dfin (T: Tree X): List X :=
  match T with
  | empty => []
  | grow x L R => search_dfin L ++ [x] ++ search_dfin R

-- Depth-first post-order
def search_dfpo (T: Tree X): List X :=
  match T with
  | empty => []
  | grow x L R => search_dfpo L ++ search_dfpo R ++ [x]

-- A tree is ordered if for every node x, if its left and right children are xL and xR,
-- then xL ≤ x ≤ xR.

def ordered [LE X] (T: Tree X): Prop :=
  match T with
  | empty => True
  | grow x L R => (ordered L ∧ ∀ xL, contains L xL → xL ≤ x) ∧ (ordered R ∧ ∀ xR, contains R xR → x ≤ xR)

theorem search_dfin_contains (T: Tree X) (x: X): x ∈ search_dfin T ↔ contains T x := by
  induction T with
  | empty => simp [search_dfin, contains]
  | grow y L R hL hR =>
    constructor
    · intro h
      rw [search_dfin, List.mem_append, List.mem_append, List.mem_singleton] at h
      rw [contains]
      cases h with
      | inl h =>
        cases h with
        | inl hLx =>
          exact Or.inr (Or.inl ((hL).mp hLx))
        | inr hxy =>
          exact Or.inl hxy.symm
      | inr hRx =>
        exact Or.inr (Or.inr ((hR).mp hRx))
    · intro h
      rw [search_dfin, List.mem_append, List.mem_append, List.mem_singleton]
      rw [contains] at h
      cases h with
      | inl hyx =>
        exact Or.inl (Or.inr hyx.symm)
      | inr h =>
        cases h with
        | inl hLx =>
          exact Or.inl (Or.inl ((hL).mpr hLx))
        | inr hRx =>
          exact Or.inr ((hR).mpr hRx)

theorem search_dfin_ordered [LE X]
    (le_trans: ∀ {a b c: X}, a ≤ b → b ≤ c → a ≤ c)
    (T: Tree X) (h: ordered T): List.Pairwise (· ≤ ·) (search_dfin T) := by
  induction T with
  | empty =>
    exact List.Pairwise.nil
  | grow x L R hL hR =>
    simp [ordered] at h
    rw [search_dfin, List.pairwise_append]
    constructor
    · rw [List.pairwise_append]
      constructor
      · exact hL h.1.1
      · constructor
        · exact List.pairwise_singleton _ x
        · intro y hy z hz
          rw [List.mem_singleton] at hz
          rw [hz]
          exact h.1.2 y ((search_dfin_contains L y).mp hy)
    · constructor
      · exact hR h.2.1
      · intro y hy z hz
        rw [List.mem_append] at hy
        cases hy with
        | inl hyL =>
          have hyx: y ≤ x := h.1.2 y ((search_dfin_contains L y).mp hyL)
          exact le_trans hyx (h.2.2 z ((search_dfin_contains R z).mp hz))
        | inr hyx =>
          rw [List.mem_singleton] at hyx
          rw [hyx]
          exact h.2.2 z ((search_dfin_contains R z).mp hz)
