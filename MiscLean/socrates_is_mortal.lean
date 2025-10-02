axiom Human : Type

axiom socrates : Human

axiom mortal : Human → Prop

axiom humans_mortal : ∀ h : Human, mortal h

theorem socrates_mortal : mortal socrates :=
  humans_mortal socrates
