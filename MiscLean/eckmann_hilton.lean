
/-

A simplified Eckmann-Hilton argument (exercise 1.1.14 in "Intro. to Categorical Logic" by Awodey & Bauer https://awodey.github.io/catlog/notes/catlogdraft.pdf)

Suppose m and m' are two binary operations on a set X such that they
- share a common unit e,
- satisfy the "swap-commute" condition, m(m'(x, y), m'(z, w)) = m'(m(x, z), m(y, w)).

Then m and m' are:
- equal (m = m')
- associative
- commutative

As a consequence if (X, m, e) is a unital magma and m is a magma homomorphism X × X → X, then (X, m, e) is a commutative monoid.

-/


variable {X: Type}

def Associative (m: X → X → X): Prop :=
  ∀ x y z, m (m x y) z = m x (m y z)

def Commutative (m: X → X → X): Prop :=
  ∀ x y, m x y = m y x

def IsUnit (m: X → X → X) (e: X): Prop :=
  (∀ x, m e x = x) ∧ (∀ x, m x e = x)

def SwapCommute (m m': X → X → X): Prop :=
  ∀ x y z w, m (m' x y) (m' z w) = m' (m x z) (m y w)



variable {m m': X → X → X} {e e': X}

theorem swap_unit_equal (h1: IsUnit m e) (h2: IsUnit m' e') (h3: SwapCommute m m'): e = e' := by
  calc
    e = m e e                  := by rw [h1.left]
     _ = m (m' e e') (m' e' e) := by rw [h2.left, h2.right]
     _ = m' (m e e') (m e' e)  := by rw [h3]
     _ = m' e' e'              := by rw [h1.left, h1.right]
     _ = e'                    := by rw [h2.right]

theorem swap_equal (h1: IsUnit m e) (h2: IsUnit m' e') (h3: SwapCommute m m'): m = m' := by
  ext x y
  rw [←h2.right x, ←h2.left y]
  rw [h3]
  rw [←swap_unit_equal h1 h2 h3]
  rw [h1.right x, h1.left y]
  rw [swap_unit_equal h1 h2 h3]
  rw [h2.right x, h2.left y]

theorem swap_self_associative (h1: IsUnit m e) (h2: SwapCommute m m): Associative m := by
  intro x y z
  rw [←h1.left z]
  rw [h2]
  rw [h1.right x]
  rw [h1.left z]

theorem swap_self_commutative (h1: IsUnit m e) (h2: SwapCommute m m): Commutative m := by
  intro x y
  rw [←h1.left x, ←h1.right y]
  rw [h2]
  rw [h1.left y, h1.right x]
  rw [h1.left x, h1.right y]



class UnitalMagma {X: Type} (m: X → X → X) (e: X): Prop where
  unit: IsUnit m e

class CommutativeMonoid {X: Type} (m: X → X → X) (e: X): Prop extends UnitalMagma m e where
  associative: Associative m
  commutative: Commutative m

-- Homomorphism and product between arbitrary magmas.

variable {X Y: Type}
variable {m m': X → X → X} {e e': X}
variable {mX: X → X → X} {mY: Y → Y → Y} {eX: X} {eY: Y}

structure homomorphism (MX: UnitalMagma mX eX) (MY: UnitalMagma mY eY) (f: X → Y): Prop where
  unit: f eX = eY
  preserve: ∀ x1 x2, f (mX x1 x2) = mY (f x1) (f x2)

theorem Product (MX: UnitalMagma mX eX) (MY: UnitalMagma mY eY): UnitalMagma (fun (x1, y1) (x2, y2) => (mX x1 x2, mY y1 y2)) (eX, eY) := {
  unit := by
    constructor
    · intro (x, y)
      simp
      exact ⟨MX.unit.left x, MY.unit.left y⟩
    · intro (x, y)
      simp
      exact ⟨MX.unit.right x, MY.unit.right y⟩
}

-- Since we will use the following pattern a lot let's give it a name.
-- If M is a unital magma (could be any algebraic object really)
-- and f is a homomorphism M × M → M, we will call f a "prod_hom" on M.

def prod_hom (M: UnitalMagma m e) (f: X → X → X): Prop :=
  homomorphism (Product M M) M (fun (x1, x2) => f x1 x2)

-- If (X, m) is a unital magma and m' is a homomorphism X × X → X between product magmas, then m swap commutes with m'.

theorem prod_hom_swap {M: UnitalMagma m e} (h: prod_hom M m'): SwapCommute m m' := by
  intro x y z w
  have := h.preserve (x, y) (z, w)
  simp at this
  rw [this]

-- If (X, m) and (X, m') are unital magmas and m' is a homomorphism X × X → X then m = m'.

theorem prod_hom_equal (M: UnitalMagma m e) (M': UnitalMagma m' e') (h: prod_hom M m'): m = m' := by
  apply swap_equal M.unit M'.unit
  exact prod_hom_swap h

-- If (X, m) and (X, m') are unital magmas and m' is a homomorphism X × X → X then then m swap commutes with itself.

theorem prod_hom_swap_self (M: UnitalMagma m e) (M': UnitalMagma m' e') (h: prod_hom M m'): SwapCommute m m := by
  rw (config := {occs := .pos [2]}) [prod_hom_equal M M' h] -- rewrite at a specific position
  exact prod_hom_swap h

-- If (X, m) and (X, m') are unital magmas and m' is a homomorphism X × X → X then (X, m) promotes to a commutative monoid.

theorem prod_hom_commutative (M: UnitalMagma m e) (M': UnitalMagma m' e') (h: prod_hom M m'): CommutativeMonoid m e := by
  constructor
  apply swap_self_associative M.unit
  exact prod_hom_swap_self M M' h
  apply swap_self_commutative M.unit
  exact prod_hom_swap_self M M' h

-- If (X, m) is a unital magma and m is a homomorphism X × X → X then (X, m) promotes to a commutative monoid.

theorem prod_hom_self_commutative (M: UnitalMagma m e) (h: prod_hom M m): CommutativeMonoid m e := by
  exact prod_hom_commutative M M h
