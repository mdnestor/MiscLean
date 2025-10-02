structure Monad2 where
  unit: Type -> Type
  bind (A B: Type): unit A -> (A -> unit B) -> unit B

def IdentityMonad : Monad2 := {
  unit := fun T => T,
  bind := by {simp; intro _ _ a f; exact f a}
}
def Subset (T: Type) : Type := T -> Prop
def singleton (T: Type) (x: T): Subset T := fun y => x = y
def PowersetMonad : Monad2 := {
  unit := Subset,
  bind := by {
    simp;
    intro A B S f;
    exact fun b: B => exists a: A, (S a) ∧ (f a b)
  }
}
structure Prob (T: Type) where
  density: T -> Float
  positive (x: T): 0 ≤ density x
def ProbMonad : Monad2 := {
  unit := fun T => Prob T,
  bind := by {
    simp;
    intro A B P f;
    exact {
      density := sorry,
      positive := sorry
    }
  }
}
structure Mealy where
  input: Type
  output: Type
  state: Type
  update: state × input → state × output
structure FMealy where
  input: Type
  output: Type
  state: Type
  M: Monad2
  update: state × input → M.unit (state × output)
def incl (M: Mealy): FMealy := {
  input := M.input, output := M.output, state := M.state,
  M := IdentityMonad,
  update := by {intro (x, y); rw [Monad2.unit, IdentityMonad]; simp; exact M.update (x, y)}
}
def DeterministicFMealyMachine (M: Mealy): FMealy := incl M
structure NondeterministicMealy where
  state: Type
  input: Type
  output: Type
  update: state × input → Subset (state × output)
def incl_nd (M: NondeterministicMealy): FMealy := {
  input := M.input,
  output := M.output,
  state := M.state,
  M := PowersetMonad,
  update := M.update
}
