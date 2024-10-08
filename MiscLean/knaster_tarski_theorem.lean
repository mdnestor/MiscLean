
-- Knaster Tarski fixed point theorem

-- https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Order/FixedPoints.lean
--
-- TODO: type class inference?

class Poset (X: Type) where
  leq: X → X → Prop
  refl: ∀ x: X, leq x x
  asymm: ∀ x y: X, leq x y ∧ leq y x → x = y
  trans: ∀ x y z: X, leq x y ∧ leq y z → leq x z

def dual (P: Poset X): Poset X := {
  leq := fun x y => P.leq y x
  refl := P.refl
  asymm := by
    intro x y ⟨h1, h2⟩
    exact P.asymm x y ⟨h2, h1⟩
  trans := by
    intro x y z ⟨h1, h2⟩
    exact P.trans z y x ⟨h2, h1⟩
}

def set (X: Type): Type :=
  X → Prop

def subset {X: Type} (A B: set X): Prop :=
  ∀ x: X, A x → B x

def Poset.lower_bound {X: Type} [Poset X] (A: set X) (x: X): Prop :=
  ∀ y: X, A y → leq x y

def Poset.greatest_lower_bound {X: Type} [Poset X] (A: set X) (x: X): Prop :=
  ∀ y: X, lower_bound A y → leq y x

def Poset.upper_bound {X: Type} [Poset X] (A: set X) (x: X): Prop :=
  ∀ y: X, A y → leq y x

def Poset.least_upper_bound {X: Type} [Poset X] (A: set X) (x: X): Prop :=
  ∀ y: X, upper_bound A y → leq x y

structure CompleteLattice (X: Type) extends Poset X where
  meet: set X → X
  join: set X → X
  meet_lower_bound: ∀ A: set X, Poset.lower_bound A (meet A)
  meet_greatest_lower_bound: ∀ A: set X, Poset.greatest_lower_bound A (meet A)
  join_upper_bound: ∀ A: set X, Poset.upper_bound A (join A)
  join_least_upper_bound: ∀ A: set X, Poset.least_upper_bound A (join A)

def monotone (P1: Poset X1) (P2: Poset X2) (f: X1 → X2): Prop :=
  ∀ x y: X1, P1.leq x y → P2.leq (f x) (f y)

def CompleteSublattice (L: CompleteLattice X) (S: set X): Prop :=
  ∀ A: set X, subset A S → S (L.meet A) ∧ S (L.join A)

def fixed_point {X: Type} (f: X → X): set X :=
  fun x => f x = x

def interval (P: Poset X) (a b: X): set X :=
  fun x => P.leq a x ∧ P.leq x b

def subset_lower_bound (P: Poset X) (A B: set X) (x: X) (h1: subset A B) (h2: Poset.lower_bound B x): Poset.lower_bound A x := by
  intro y y_in_A
  have y_in_B := h1 y y_in_A
  exact h2 y y_in_B

def subset_upper_bound (P: Poset X) (A B: set X) (x: X) (h1: subset A B) (h2: Poset.upper_bound B x): Poset.upper_bound A x := by
  intro y y_in_A
  have y_in_B := h1 y y_in_A
  exact h2 y y_in_B

theorem interval_lower_bound (P: Poset X) (a b: X): Poset.lower_bound (interval P a b) a := by
  intro y hy
  exact hy.1

theorem interval_greatest_lower_bound (P: Poset X) (a b: X): Poset.greatest_lower_bound (interval P a b) a := by
  intro y hy
  exact hy a ⟨P.refl a, h⟩

theorem interval_upper_bound (P: Poset X) (a b: X): Poset.upper_bound (interval P a b) b := by
  intro y hy
  exact hy.2

theorem interval_least_upper_bound (P: Poset X) (a b: X) (h: P.leq a b): Poset.least_upper_bound (interval P a b) b := by
  intro y hy
  exact hy b ⟨h, P.refl b⟩

theorem interval_complete_sublattice (L: CompleteLattice X) (a b: X) (h: L.leq a b): CompleteSublattice L (interval L.toPoset a b) := by
  intro A hA
  apply And.intro
  rw [interval]
  apply And.intro
  have h1 := interval_lower_bound L.toPoset a b
  have h2 := subset_lower_bound L.toPoset A (interval L.toPoset a b) a hA h1
  exact L.meet_greatest_lower_bound A a h2
  sorry
  apply And.intro
  sorry
  sorry

def whole (X: Type): set X :=
  fun _ => True

def image (f: X → Y) (S: set X): set Y :=
  fun y => ∃ x: X, S x ∧ f x = y

theorem TarskiFixedPointLemma (L: CompleteLattice X) (f: X → X) (h1: monotone L.toPoset L.toPoset f): (fixed_point f) (L.join (fixed_point f))  := by
  let P: set X := fun x => L.leq x (f x)
  let p := L.join P
  let x: X := sorry
  have h1: L.leq x p := sorry
  have h2: L.leq (f x) (f p) := sorry
  have h3: L.leq x (f x) := sorry
  have h4: L.leq x (f p) := sorry
  /-
  have h5: Poset.upper_bound P (f p) := sorry
  have h6: L.leq p (f p) := sorry
  have h7: L.leq (f p) (f (f p)) := sorry
  have h8: P (f p) := sorry
  have h9: L.leq (f p) p := sorry
  have h10: f p = p := sorry
  have h11: P p := sorry
  repeat rw [fixed_point]
  have h12: p = L.join P := rfl
  have h13: subset (fixed_point f) P := sorry
  have h14: L.join (fixed_point f) = p := sorry
  rw [h14, h10]
  -/
  sorry

theorem TarskiFixedPointTheorem (L: CompleteLattice X) (f: X → X) (h1: monotone L.toPoset L.toPoset f): CompleteSublattice L (fixed_point f) := by
  let P := fixed_point f
  let D: set X := fun x => L.leq x (f x)
  let x: X := sorry
  have h1: D x := sorry
  let u := L.join D
  have h2: D u := sorry
  have h3: f u = u := sorry
  /-
  have h4: least_upper_bound L.toPoset D u := sorry
  let one_L := L.join (whole X)
  intro W
  intro hW
  let w := L.join W
  have h5: subset (image f (interval L.toPoset w one_L)) (interval L.toPoset w one_L) := sorry
  apply And.intro
  sorry
  -/
  sorry
