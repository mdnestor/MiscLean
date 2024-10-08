/-
Let X and T be sets.
Suppose T is equipped with a binary operation, and let • be a left action of T on X.
-/

import Mathlib.Algebra.Group.Action.Defs

-- suppose T acts on both X and Y
-- a function f: X → Y is called T-equivariant if f (t • x) = t • (f x) for all t and x
def equivariant {X Y: Type} (T: Type) [SMul T X] [SMul T Y] (f: X → Y): Prop :=
  ∀ t: T, ∀ x: X, f (t • x) = t • (f x)

-- f is called T-invariant if f (t • x) = f x for all t and x
def invariant {X Y: Type} (T: Type) (f: X → Y) [SMul T X]: Prop :=
  ∀ t: T, ∀ x: X, f (t • x) = f x

-- the identity function is equivariant
theorem equivariant_id {X T: Type} [SMul T X] [SMul T Y]: equivariant T (@id X) := by
  repeat intro
  rfl

-- if f and g are equivariant then g ∘ f is equivariant
theorem equivariant_comp {X Y Z T: Type} [SMul T X] [SMul T Y] [SMul T Z] {f: X → Y} {g: Y → Z} (hf: equivariant T f) (hg: equivariant T g): equivariant T (g ∘ f) := by
  repeat intro
  repeat rw [Function.comp_apply]
  rw [hf, hg]

-- if f is invariant then g ∘ f is invariant for all g.
theorem invariant_comp {X Y Z T: Type} [SMul T X] [SMul T Y] [SMul T Z] {f: X → Y} (hf: invariant T f) (g: Y → Z): invariant T (g ∘ f) := by
  repeat intro
  repeat rw [Function.comp_apply]
  rw [hf]

-- if f is equivariant and g is invariant then g ∘ f is invariant
theorem equivariant_invariant_comp {X Y Z T: Type} [SMul T X] [SMul T Y] [SMul T Z] {f: X → Y} {g: Y → Z} (hf: equivariant T f) (hg: invariant T g): invariant T (g ∘ f) := by
  repeat intro
  repeat rw [Function.comp_apply]
  rw [hf, hg]
