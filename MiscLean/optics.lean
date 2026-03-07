
-- Lenses and optics.

-- https://ncatlab.org/nlab/show/lens+%28in+computer+science%29
-- https://ncatlab.org/nlab/show/optic+%28in+computer+science%29
-- https://golem.ph.utesas.edu/category/2020/01/profunctor_optics_the_categori.html


variable {S T A B X Y: Type}



-- A "lens" is a data structure consisting of two sets S and A
-- and two functions view: S → A and update: S × A → S.

-- The idea is that S is like a large database, and A is like a single readout from it.
-- A lens is like a way to view a large object at one of its parts, as well as update it with a new part.

structure Lens (S A: Type) where
  view: S → A
  update: S × A → S

-- A lens is called "lawful" if it satisfies some natural conditions:
structure LawfulLens (S A: Type) extends Lens S A where
  putget: ∀ s a, view (update (s, a)) = a
  getput: ∀ s, update (s, view s) = s
  putput: ∀ s a₁ a₂, update (update (s, a₁), a₂) = update (s, a₂)


-- We can compose lenses: suppose A is itself a database with even smaller part B.
-- Then we can view S from B by first viewing S from A and then viewing A from B.
-- We can also update S at B by first updating A at B, and then updating S at A.

def Lens.comp (f: Lens S A) (g: Lens A B): Lens S B := {
  view := g.view ∘ f.view
  update := fun (s, b) => f.update (s, g.update (f.view s, b))
}


namespace Optic

-- The above definition is called a "monomorphic" lens.
-- In general, we can allow the original "large" object S and the updated "large" object T to be different types.
-- Also we can let the readout A to be different than the update B.

structure Lens (S T: Type) (A B: Type) where
  view: S → A
  update: S × B → T

def Lens.comp (f: Lens S T A B) (g: Lens A B X Y): Lens S T X Y := {
  view := g.view ∘ f.view
  update := fun (s, y) => f.update (s, g.update (f.view s, y))
}

-- Several variations on the theme: can you catch the pattern?

structure Prism (S T: Type) (A B: Type) where
  pmatch: S → Sum A T
  build: B → T

structure Traversal (S T: Type) (A B: Type) where
  estract: S → Σ n, Vector A n × (Vector B n → T)

structure Grate (S T: Type) (A B: Type) where
  distribute: ((S → A) → B) → T



-- In general all the above data structures are special cases of an optic.
-- In particular they each correspond to a different choice of monoidal operation `m`,
-- where a lens corresponds to the Cartesian product.

structure Optic (m: Type → Type → Type) (S T: Type) (A B: Type) where
  res: Type
  view: S → m res A
  update: m res B → T

example (f: Optic Prod S T A B): Lens S T A B := {
  view := fun s => (f.view s).snd
  update := fun (s, b) => f.update ((f.view s).fst, b)
}

-- TODO

example (f: Optic Sum S T A B): Prism S T A B := {
  pmatch := sorry
  build := sorry
}

def Exp (α β: Type): Type :=
  α → β

example (f: Optic Esp S T A B): Grate S T A B := {
  distribute := sorry
}

-- TODO: define composition of optics.
-- This requires the monoid associavitity law.

def Optic.comp (m: Type → Type → Type) (f: Optic m S T A B) (g: Optic m A B X Y): Optic m S T X Y := {
  res := f.res × g.res
  view := sorry
  update := sorry
}

def Optic.equiv (m: Type → Type → Type) (f₁ f₂: Optic m S T A B): Prop :=
  sorry



-- Appendix: parameterized and coparameterized maps.
-- https://arxiv.org/pdf/2105.06332

structure Para (S A: Type) where
  param: Type
  map: param → S → A

def Para.comp (f: Para S A) (g: Para A X): Para S X := {
  param := f.param × g.param
  map := fun (θ₁, θ₂) s => g.map θ₂ (f.map θ₁ s)
}

structure CoPara (S A: Type) where
  param: Type
  map: S → A × param

def CoPara.comp (f: CoPara S A) (g: CoPara A X): CoPara S X := {
  param := f.param × g.param
  map := fun s =>
    let (y, θ₁) := f.map s
    let (z, θ₂) := g.map y
    (z, (θ₁, θ₂))
}

