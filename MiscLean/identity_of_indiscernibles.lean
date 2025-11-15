-- Identity of indiscernibles: two objects are equal iff. they share all properties.
-- forward direction is obvious.
-- For the reverse, suppose x and y share all properties.
-- Consider the property of "being equal to x" :)

theorem identity_of_indiscernibles {X: Type} (x y: X): x = y ↔ ∀ p: X → Prop, p x ↔ p y := by
  apply Iff.intro
  · intro h _
    rw [h]
  · intro h
    rw [←h (fun z => x = z)]
