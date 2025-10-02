Collection of miscellaneous finished and unfinished Lean 4 formalizations.

# How to build

Requires [Lake](https://github.com/leanprover/lake).

```sh
git clone https://github.com/mdnestor/MiscLean
cd MiscLean
lake build
```
# Learning resources

- Lean homepage: [lean-lang.org](https://lean-lang.org/)
- Lean community homepage: [leanprover-community.github.io](https://leanprover-community.github.io/)
- Documentation
  - [mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/)
  - [Lean4 docs](https://lean-lang.org/lean4/doc/)
- Services
  - [Lean 4 Web](https://live.lean-lang.org/) - online compiler with mathlib installed
  - [Loogle](https://loogle.lean-lang.org/) - Lean4/Mathlib library search tool
  - [Lean Zulip chat](leanprover.zulipchat.com)
- Books
  - [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
  - [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
  - [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/)

Sample code: proof that composition of surjective functions is surjective.

```lean
def surjective {X Y: Type} (f: X → Y): Prop :=
  ∀ y: Y, ∃ x: X, f x = y

theorem surjective_comp {X Y Z: Type} {f: X → Y} {g: Y → Z}
  (hf: surjective f) (hg: surjective g): surjective (g ∘ f) := by
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  exists x
  simp [hx, hy]
```

Bonus: proof of Cantor's theorem

```lean
def Set (X: Type): Type :=
  X → Prop

theorem cantor (f: X → Set X): ¬ surjective f := by
  intro h
  let S := fun x => ¬ (f x) x
  obtain ⟨z, hz⟩ := h S
  have: ∀ x: X, S x ↔ ¬ (f x) x := by simp
  have := this z
  rw [hz] at this
  simp_all
```