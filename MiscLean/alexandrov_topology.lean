import Mathlib.Order.SetNotation

variable {X: Type*}

structure TopSpace (T: Set (Set X)): Prop where
  univ: Set.univ ∈ T
  empty: ∅ ∈ T
  union: ∀ C: Set (Set X), (∀ A ∈ C, A ∈ T) → Set.sUnion C ∈ T
  inter: ∀ A B: Set X, A ∈ T → B ∈ T → A ∩ B ∈ T

structure AlexandrovSpace (T: Set (Set X)): Prop extends TopSpace T where
  inter': ∀ C: Set (Set X), (∀ A ∈ C, A ∈ T) → Set.sInter C ∈ T

def upper (r: X → X → Prop) (A: Set X): Prop :=
  ∀ x y, x ∈ A → r x y → y ∈ A

theorem upper_inter {r: X → X → Prop} {A B: Set X} (hA: upper r A) (hB: upper r B): upper r (A ∩ B) := by
  intro x y h1 h2
  constructor
  . exact hA x y h1.left h2
  . exact hB x y h1.right h2

def UpperSets (r: X → X → Prop): Set (Set X) :=
  {A | upper r A}

example (r: X → X → Prop): AlexandrovSpace (UpperSets r) := {
  univ := by
    intro _ _ _ _
    trivial
  empty := by
    intro _ _ _
    contradiction
  union := by
    intro _ h1 _ _ ⟨U, h2⟩ h3
    exists U
    constructor
    exact h2.left
    apply h1
    exact h2.left
    exact h2.right
    exact h3
  inter := by
    intro _ _ h1 h2 _ _ h3 h4
    apply upper_inter h1 h2
    . exact h3
    . exact h4
  inter' := by
    intro C h1 x y h2 h3 A hA
    apply h1 A hA x
    exact h2 A hA
    exact h3
}
