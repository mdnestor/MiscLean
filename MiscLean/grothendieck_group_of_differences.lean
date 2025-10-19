/-

Construction of the group of difference of a commutative monoid, aka the Grothendeick group.
https://en.wikipedia.org/wiki/Grothendieck_group

E.g. how the integers are constructed from the naturals.

-/

-- Step 1: define the equivalence relation on a commutative monoid.

class CommMonoid (α: Type u) [Add α] [Zero α] where
  assoc: ∀ {x y z: α}, (x + y) + z = x + (y + z)
  comm: ∀ x y: α, x + y = y + x
  add_zero: ∀ x: α, x + 0 = x

variable {α: Type u} [Add α] [Zero α]

theorem CommMonoid.zero_add (M: CommMonoid α): ∀ x: α, 0 + x = x := by
  intro x
  rw [M.comm, M.add_zero]

def relation (α: Type u) [Add α]: α × α → α × α → Prop :=
  λ (a₁, a₂) (b₁, b₂) ↦ ∃ k, a₁ + b₂ + k = b₁ + a₂ + k

instance: HasEquiv (α × α) := {
  Equiv := relation α
}

theorem equivalence (M: CommMonoid α): Equivalence (relation α) := {
  refl := by
    intro
    exists 0
  symm := by
    intro _ _ ⟨k, hk⟩
    exists k
    exact (Eq.symm hk)
  trans := by
    intro (x₁, x₂) (y₁, y₂) (z₁, z₂) ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩
    exists y₁ + y₂ + k₁ + k₂
    calc
      x₁ + z₂ + (y₁ + y₂ + k₁ + k₂)
      _ = (x₁ + y₂ + k₁) + (y₁ + z₂ + k₂) := by sorry -- tedious, not sure how to automate?
      _ = (y₁ + x₂ + k₁) + (z₁ + y₂ + k₂) := by rw [hk₁, hk₂]
      _ = z₁ + x₂ + (y₁ + y₂ + k₁ + k₂) := by sorry
}

def setoid (M: CommMonoid α): Setoid (α × α) := {
  r := relation α
  iseqv := equivalence M
}

def quotient (M: CommMonoid α): Type u :=
  Quotient (setoid M)

-- Part 2: lift the addition operation to the quotient.

instance: Zero (α × α) := {
  zero := (0, 0)
}

instance (M: CommMonoid α): Zero (quotient M) := {
  zero := Quotient.mk _ 0
}

instance: Add (α × α) := {
  add := fun (x₁, x₂) (y₁, y₂) => (x₁ + y₁, x₂ + y₂)
}

theorem quotient_add {M: CommMonoid α} (a b c d: α × α) (h₁: a ≈ c) (h₂: b ≈ d):
  Quotient.mk (setoid M) (a + b) = Quotient.mk (setoid M) (c + d) := by
  apply Quotient.sound
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  exists k₁ + k₂
  calc
    a.fst + b.fst + (c.snd + d.snd) + (k₁ + k₂)
    _ = (a.fst + c.snd + k₁) + (b.fst + d.snd + k₂) := by sorry
    _ = (c.fst + a.snd + k₁) + (d.fst + b.snd + k₂) := by rw [hk₁, hk₂]
    _ = c.fst + d.fst + (a.snd + b.snd) + (k₁ + k₂) := by sorry

instance (M: CommMonoid α): Add (quotient M) := {
  add := λ x y ↦ Quotient.liftOn₂ x y _ quotient_add
}

theorem quotient_neg {M: CommMonoid α} (a b: α × α) (h: a ≈ b):
  Quotient.mk (setoid M) (Prod.swap a) = Quotient.mk (setoid M) (Prod.swap b) := by
  apply Quotient.sound
  obtain ⟨k, hk⟩ := h
  exists k
  calc
    a.snd + b.fst + k
    _ = b.fst + a.snd + k := by rw [M.comm a.snd]
    _ = a.fst + b.snd + k := by rw [hk]
    _ = b.snd + a.fst + k := by rw [M.comm a.fst]

instance (M: CommMonoid α): Neg (quotient M) := {
  neg := λ x ↦ Quotient.liftOn x _ quotient_neg
}

-- Step 3: show the quotient forms a commutative group.

instance [Add α] [Neg α]: Sub α := {
  sub := λ a b ↦ a + -b
}

class CommGroup (α: Type u) [Add α] [Zero α] [Neg α] extends CommMonoid α where
  add_neg: ∀ a: α, a - a = 0

def GrothendieckGroup (M: CommMonoid α): CommGroup (quotient M) := {
  assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂)
    apply Quotient.sound
    exists 0
    calc
      ((a₁ + b₁) + c₁) + (a₂ + (b₂ + c₂)) + 0
      _ = (a₁ + (b₁ + c₁)) + ((a₂ + b₂) + c₂) + 0 := by repeat rw [M.assoc]
  comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro (a₁, a₂) (b₁, b₂)
    apply Quotient.sound
    exists 0
    calc
      a₁ + b₁ + (b₂ + a₂) + 0
      _ = b₁ + a₁ + (a₂ + b₂) + 0 := by rw [M.comm a₁, M.comm a₂]
  add_zero := by
    intro x
    refine Quotient.inductionOn x ?_
    intro (a₁, a₂)
    apply Quotient.sound
    exists 0
    calc
      a₁ + 0 + a₂ + 0
      _ = a₁ + (a₂ + 0) + 0 := by repeat rw [M.add_zero]
  add_neg := by
    intro x
    refine Quotient.inductionOn x ?_
    intro (a₁, a₂)
    apply Quotient.sound
    exists 0
    calc
      a₁ + a₂ + 0 + 0
      _ = a₁ + a₂ := by repeat rw [M.add_zero]
      _ = a₂ + a₁ := by rw [M.comm]
      _ = 0 + (a₂ + a₁) + 0 := by rw [M.zero_add, M.add_zero]
}
