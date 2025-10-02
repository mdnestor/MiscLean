
import Mathlib.Data.Set.Basic

-- The "graph" of a function f: X → Y is the set of points of the form (x, f(x))

def graph (f: X → Y): Set (X × Y) :=
  Set.range fun x => (x, f x)

-- The vertical line test says that a subset S ⊆ X × Y is the graph of a function if and only if
-- for all x, there exists unique y such that (x, y) ∈ S.

theorem vertical_line_test (S: Set (X × Y)): (∃ f, S = graph f) ↔ ∀ x, ∃! y, (x, y) ∈ S := by
  constructor
  . intro h x
    obtain ⟨f, hf⟩ := h
    exists f x
    simp_all [graph]
  . intro h
    exists fun x => Classical.choose (h x)
    ext ⟨x, y⟩
    have := Classical.choose_spec (h x)
    constructor
    . intro h1
      simp [this.right y h1, graph]
    . intro h1
      simp [graph] at h1
      rw [←h1]
      exact this.left
