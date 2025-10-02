
-- `Rel X` is the type of relations on `X`

def Rel (X: Type u): Type u :=
  X → X → Prop

-- given an arbitrary relation `R`, then `Path R` is the type of paths

inductive Path (R: Rel X): Rel X where
| nil: R x y → Path R x y
| cons: R x y → Path R y z → Path R x z

def trans (R: Rel X): Prop :=
  ∀ x y z, R x y → R y z → R x z

-- `Path R` is always transitive

theorem path_trans (R: Rel X): trans (Path R) := by
  intro _ _ _ h1 h2
  induction h1 with
  | nil h0 => exact Path.cons h0 h2
  | cons h3 _ hi => exact Path.cons h3 (hi h2)

def refl (R: Rel X): Prop :=
  ∀ x, R x x

-- if `R` is reflexive, then so is `Path R`

theorem path_refl (R: Rel X) (h: refl R): refl (Path R) := by
  intro x
  exact Path.nil (h x)
