
def subset (X: Type): Type := X -> Prop
def whole (X: Type): subset X := fun _ => True
def empty (X: Type): subset X := fun _ => False
def subset.complement {X: Type} (S: subset X): subset X := fun x => ¬ S x
def cup {X: Type} (A B: subset X): subset X := fun x => A x ∨ B x
def cap {X: Type} (A B: subset X): subset X := fun x => A x ∧ B x
def setminus {X: Type} (A B: subset X): subset X := cap A B.complement
def symmdiff {X: Type} (A B: subset X): subset X := setminus (cup A B) (cap A B)

example (X: Type): empty X = subset.complement (whole X) :=
  by funext; rw [empty, subset.complement, whole]; simp
example (X: Type): forall S: subset X, cup S S.complement = whole X :=
  sorry
example (X: Type): forall S: subset X, cap S S.complement = empty X :=
  sorry
example (X: Type): forall S: subset X, cup S (empty X) = S :=
  by intros; funext; rw [cup, empty]; simp
example (X: Type): forall S: subset X, cup S (whole X) = whole X :=
  by intros; funext; rw [cup, whole]; simp
example (X: Type): forall S: subset X, cap S (empty X) = empty X :=
  by intros; funext; rw [cap, empty]; simp
example (X: Type): forall S: subset X, cap S (whole X) = S :=
  by intros; funext; rw [cap, whole]; simp
example (X: Type): forall A B C: subset X, cup A (cup B C) = cup (cup A B) C :=
  by intros; funext; rw [cup, cup, cup, cup]; sorry
example (X: Type): forall A B C: subset X, cap A (cap B C) = cap (cap A B) C :=
  by intros; funext; rw [cap, cap, cap, cap]; sorry
/- De Morgan's laws -/
example (X: Type): forall A B: subset X, (cap A B).complement = cup A.complement B.complement :=
  sorry
example (X: Type): forall A B: subset X, (cup A B).complement = cap A.complement B.complement :=
  sorry


def injective {X Y: Type} (f: X -> Y): Prop := forall x1 x2: X, f x1 = f x2 -> x1 = x2
def surjective {X Y: Type} (f: X -> Y): Prop := forall y: Y, exists x: X, f x = y
def bijective {X Y: Type} (f: X -> Y): Prop := injective f ∧ surjective f

theorem injective_implies_surjective {X Y: Type}: (exists f: X -> Y, injective f) -> (exists g: Y -> X, surjective g) := sorry

theorem surjective_implies_injective {X Y: Type}: (exists f: X -> Y, surjective f) -> (exists g: Y -> X, injective g) := sorry

theorem injective_composition {X Y Z: Type} (f: X -> Y) (g: Y -> Z): injective f ∧ injective g -> injective (g ∘ f) := by
  intro h1
  rw [injective]
  intro x1 x2
  simp
  intro h2
  have h3: f x1 = f x2 := by apply h1.2; exact h2;
  apply h1.1
  exact h3

theorem surjective_composition {X Y Z: Type} (f: X -> Y) (g: Y -> Z): surjective f ∧ surjective g -> surjective (g ∘ f) := by
  sorry

theorem bijective_composition {X Y Z: Type} (f: X -> Y) (g: Y -> Z): bijective f ∧ bijective g -> bijective (g ∘ f) := by
  intro h
  rw [bijective]
  apply And.intro
  apply injective_composition
  apply And.intro
  exact h.1.1
  exact h.2.1
  apply surjective_composition
  apply And.intro
  exact h.1.2
  exact h.2.2

theorem bijective_inverse {X Y: Type} (f: X -> Y): bijective f -> exists g: Y -> X, bijective g := sorry

def equinumerous (X Y: Type): Prop := exists f: X -> Y, bijective f

example (X Y: Type): (exists f: X -> Y, bijective f) -> equinumerous X Y := by intro h; rw [equinumerous]; exact h

/- Cantor's theorem -/
theorem CantorsTheorem (X: Type): forall f: X -> (subset X), ¬ surjective f := sorry

example (X: Type): ¬ equinumerous X (subset X) := sorry

def countable (X: Type): Prop := exists f: Nat -> X, surjective f

example (X: Type): (exists f: X -> Nat, injective f) -> countable X := sorry

/- Schröder–Bernstein theorem: https://en.wikipedia.org/wiki/Schr%C3%B6der%E2%80%93Bernstein_theorem -/
/- idk if this is even true for types -/
theorem SchroderBernstein (X Y: Type): (exists f: X -> Y, injective f) ∧ (exists g: Y -> X, injective g) -> equinumerous X Y := sorry

def image {X Y: Type} (f: X -> Y) (S: subset X): subset Y := fun y => exists x: X, S x ∧ f x = y
def preimage {X Y: Type} (f: X -> Y) (S: subset Y): subset X := fun x => S (f x)

def subsetfamily (X: Type): Type := subset (subset X)

def bigcup {X: Type} (F: subsetfamily X): subset X := fun x => exists S: subset X, F S ∧ S x
def bigcap {X: Type} (F: subsetfamily X): subset X := fun x => forall S: subset X, F S ∧ S x

example {X: Type}: forall F: subsetfamily X, F (whole X) -> bigcup F = whole X := by intros; funext; rw [bigcup, whole]; sorry
example {X: Type}: forall F: subsetfamily X, F (empty X) -> bigcap F = empty X := by intros; funext; rw [bigcap, empty]; sorry

