-- defines the free monoid over a type as the type of lists of that type
-- shows that `List.map` is a monoid homomorphism between free monoids
-- also shows the free monoid over the unit type is isomorphic to the natural numbers

-- definition of a monoid
structure Monoid (X: Type) where
  op: X → X → X
  unit: X
  assoc: ∀ x y z: X, op (op x y) z = op x (op y z)
  unit_left: ∀ x: X, op unit x = x
  unit_right: ∀ x: X, op x unit = x

-- the monoid of natural numbers with addition
def NatMonoid: Monoid Nat := {
  op := Nat.add
  unit := Nat.zero
  assoc := Nat.add_assoc
  unit_left := Nat.zero_add
  unit_right := Nat.add_zero
}

-- the free monoid over an alphabet
def FreeMonoid (X: Type): Monoid (List X) := {
  op := List.append
  unit := List.nil
  assoc := List.append_assoc
  unit_left := List.nil_append
  unit_right := List.append_nil
}

-- the monoid of functions from a type to itself
-- aka the monoid of endofunctions
def FuncMonoid (X: Type): Monoid (X → X) := {
  op := fun f g => f ∘ g
  unit := id
  assoc := by intros; rfl
  unit_left := by intro; rfl
  unit_right := by intro; rfl
}

-- monoid homomorphism
structure Homomorphism (M: Monoid X) (N: Monoid Y) where
  func: X → Y
  preserve_op: ∀ x1 x2: X, func (M.op x1 x2) = N.op (func x1) (func x2)
  preserve_unit: func M.unit = N.unit

-- a function between alphabets extends to a homomorphism between free monoids
def FreeHomomorphism {X Y: Type} (f: X → Y): Homomorphism (FreeMonoid X) (FreeMonoid Y) := {
  func := List.map f
  preserve_op := by simp [FreeMonoid]
  preserve_unit := by rfl
}

-- the length homomorphism from a free monoid to the monoid of natural numbers
def LengthHomomorphism (X: Type): Homomorphism (FreeMonoid X) NatMonoid := {
  func := List.length
  preserve_op := List.length_append
  preserve_unit := List.length_nil
}

def injective (f: X → Y): Prop :=
  ∀ x1 x2: X, f x1 = f x2 → x1 = x2

def surjective (f: X → Y): Prop :=
  ∀ y: Y, ∃ x: X, f x = y

def bijective (f: X → Y): Prop :=
  injective f ∧ surjective f

-- monoid isomorphism
structure Isomorphism (M: Monoid X) (N: Monoid Y) extends Homomorphism M N where
  bijective: bijective func

-- Unit is a type containing one element (aka a singleton set)
-- if two lists containing units have the same length, they are equal
theorem unit_list_lemma {L1 L2 : List Unit} (h: L1.length = L2.length): L1 = L2 := by
  apply List.ext_getElem
  assumption
  intros
  rfl

-- the free monoid on a one-element set is isomorphic to the monoid of natural numbers
example: Isomorphism (FreeMonoid Unit) NatMonoid := {
  func := List.length
  preserve_op := List.length_append
  preserve_unit := List.length_nil
  bijective := by
    apply And.intro
    intro L1 L2 h
    exact unit_list_lemma h
    intro n
    exists List.replicate n Unit.unit
    simp
}

-- the iterates of a function
-- iterate f n = f^(n)
def iterate (f: X → X) (n: Nat): X → X :=
  match n with
  | Nat.zero => id
  | Nat.succ p => (iterate f p) ∘ f

theorem iterate_zero (f: X → X): iterate f 0 = id := rfl

theorem iterate_one (f: X → X): iterate f 1 = f := rfl

theorem Function.comp_assoc (f: Z → W) (g: Y → Z) (h: X → Y): (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

theorem iterate_add (f: X → X) (m n: Nat): iterate f m ∘ iterate f n = iterate f (m + n) := by
  induction n with
  | zero => simp [iterate_zero, Function.comp_def]
  | succ p h => simp [iterate, ←Function.comp_assoc, h]

-- given a type X and a function f: X → X
-- there is a monoid from the natural numbers to the monoid of functions on X
def FuncHomomorphism (X: Type) (f: X → X): Homomorphism NatMonoid (FuncMonoid X) := {
  func := iterate f
  preserve_op := by
    intros
    simp [FuncMonoid, NatMonoid, ←iterate_add f]
  preserve_unit := rfl
}

-- definition of a monoid action
structure MonoidAction (M: Monoid X) (Y: Type) where
  act: X → Y → Y
  preserve_mul: ∀ x1 x2: X, ∀ y: Y, act x1 (act x2 y) = act (M.op x1 x2) y
  preserve_unit: ∀ y: Y, act M.unit y = y

-- given a function f: X → X the iterates define an action of the monoid Nat
def NatAction (f: X → X): MonoidAction NatMonoid X := {
  act := iterate f
  preserve_mul := by
    intros
    simp [NatMonoid, ←iterate_add f]
  preserve_unit := by intro; rfl
}
