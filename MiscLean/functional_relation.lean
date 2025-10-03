
-- `Relation X Y` is the type of all relations from `X` to `Y`.

def Relation (X Y: Type): Type :=
  X → Y → Prop

-- we can define "exists unique" as a structured proposition with 2 fields.

structure exists_unique {X: Type} (P: X → Prop): Prop where
  exist: ∃ x, P x
  unique: ∀ x x', P x → P x' → x = x'

-- a relation is called functional if every `y` is related to a unique `x`.

def functional {X Y: Type} (R: Relation X Y): Prop :=
  ∀ x, exists_unique (λ y ↦ R x y)

-- given a function, there is a corresponding relation defined R(x, y) ↔ f(x) = y; in other words R is induced by f.

def function_relation {X Y: Type} (f: X → Y): Relation X Y :=
  λ x y ↦ f x = y

-- theorem: a relation is functional iff. it is induced by some function.

theorem functional_iff_function_relation {X Y: Type} (R: Relation X Y): functional R ↔ ∃ f, R = function_relation f := by
  constructor
  · -- suppose R is functional
    -- define f by choosing for each x the unique y such that x relates to y
    intro h
    exists λ x ↦ Classical.choose (h x).exist
    simp [Relation]
    ext x
    obtain ⟨hx1, hx2⟩ := h x
    let hy' := Classical.choose_spec hx1
    constructor
    · apply hx2
      exact hy'
    · intro h1
      rw [←h1]
      exact hy'
  · -- suppose R is induced by f
    -- to show R is functional, let x in X
    -- want to show f(x) is uniquely related to x
    intro h
    obtain ⟨f, hf⟩ := h
    rw [hf]
    intro x
    constructor
    · exists f x
    · simp_all [function_relation]
