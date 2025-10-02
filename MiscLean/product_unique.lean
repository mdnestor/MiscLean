
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Defs

-- universal property of product
def product {X1 X2 P: Type} (π1: P → X1) (π2: P → X2): Prop :=
  ∀ Y: Type, ∀ f1: Y → X1, ∀ f2: Y → X2, ∃! f: Y → P, (π1 ∘ f = f1 ∧ π2 ∘ f = f2)

theorem product_unique {X1 X2 P P': Type} {π1: P → X1} {π2: P → X2} {π1': P' → X1} {π2': P' → X2} (h: product π1 π2) (h': product π1' π2'): ∃! g: P' → P, Function.Bijective g ∧ π1 ∘ g = π1' ∧ π2 ∘ g = π2' := by
  obtain ⟨g, ⟨hg1, hg2⟩, hg3⟩ := h P' π1' π2'
  exists g
  repeat constructor
  sorry
  sorry
  constructor
  repeat assumption
  simp_all
