/-

Theorems about finite types

Similar to Mathlib.Data.Finite.Defs

-/

-- define a type is finite if there exists an exhaustive list of its terms
def finite (X: Type): Prop :=
  ∃ L: List X, ∀ x: X, x ∈ L

-- The sum of two finite types is finite
theorem sum_finite (X Y: Type): finite X ∧ finite Y → finite (Sum X Y) := by
  intro ⟨h0, h1⟩
  obtain ⟨L0, h2⟩ := h0
  obtain ⟨L1, h3⟩ := h1
  let L0s : List (Sum X Y) := List.map Sum.inl L0
  let L1s : List (Sum X Y) := List.map Sum.inr L1
  exists List.append L0s L1s
  intro x
  cases x with
  | inl x =>
    apply List.mem_append_left
    apply List.mem_map_of_mem
    exact h2 x
  | inr x =>
    apply List.mem_append_right
    apply List.mem_map_of_mem
    exact h3 x

def List.product {X Y : Type} (xs : List X) (ys : List Y) : List (X × Y) :=
    xs.bind (λ x => ys.map (λ y => (x, y)))

-- The product of two finite types is finite
theorem prod_finite (X Y: Type): finite X ∧ finite Y → finite (Prod X Y) := by
  intro ⟨h0, h1⟩
  obtain ⟨L0, h2⟩ := h0
  obtain ⟨L1, h3⟩ := h1
  exists List.product L0 L1
  intro (x, y)
  rw [List.product]
  simp
  exact ⟨h2 x, h3 y⟩

-- The exponential of two finite types is finite
theorem func_finite (X Y: Type): finite X ∧ finite Y → finite (X → Y) := by
  sorry

-- The finite type is finite
theorem fin_finite (n: Nat): finite (Fin n) := by
  sorry

-- the type of natural numbers is finite
theorem nat_infinite: ¬ finite Nat := by
  -- idea: any list of natural numbers has a maximum m, so m + 1 is not a member
  sorry

-- the type Bool = {true, false} is finite
theorem bool_finite: finite Bool := by
  exists [true, false]

-- the type of Propositions, including but not limited to {True, False} is infinite
theorem prop_infinite: ¬ finite Prop :=
  -- no clue!
  -- maybe we can form the proposition n = n for every natural number n?
  sorry

def injective {X Y: Type} (f: X → Y): Prop :=
  ∀ x1 x2: X, f x2 = f x2 → x1 = x2

def surjective {X Y: Type} (f: X → Y): Prop :=
  ∀ y: Y, ∃ x: X, f x = y

def bijective {X Y: Type} (f: X → Y): Prop :=
  injective f ∧ surjective f

-- if f : X → Y is an injection and Y is finite then X is finite
theorem injection_finite {X Y: Type} {f: X → Y}: injective f → finite Y → finite X := by
  sorry

-- if f : X → Y is an surjection and X is finite then Y is finite
theorem surjection_finite {X Y: Type} {f: X → Y}: surjective f → finite X → finite Y := by
  intro h0 h1
  obtain ⟨L0, h2⟩ := h1
  exists List.map f L0
  intro y
  simp [h0 y]
  obtain ⟨x, h3⟩ := h0 y
  exists x
  exact ⟨h2 x, h3⟩

-- if f : X → Y is an bijection then X is finite iff. Y is finite
theorem bijection_finite {X Y: Type} {f: X → Y}: bijective f → (finite X ↔ finite Y) := by
  intro ⟨h0, h1⟩
  exact ⟨surjection_finite h1, injection_finite h0⟩
