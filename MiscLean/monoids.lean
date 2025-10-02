/-
Defining monoids.
Given a type T,
T -> T -> T is equivalent to T x T -> T,
aka a binary operation
-/

def associative (T : Type) (op: T -> T -> T) : Prop :=
  ∀ a b c : T, op (op a b) c = op a (op b c)

def is_identity (T : Type) (op : T -> T -> T) (e : T): Prop :=
  ∀ a : T, op a e = a ∧ op e a = a

def has_identity (T : Type) (op: T -> T -> T) : Prop :=
  ∃ e : T, is_identity T op e

def commutative (T : Type) (op: T -> T -> T) : Prop :=
  ∀ a b : T, op a b = op b a

structure Monoid where
  T : Type
  op : T -> T -> T
  id : T
  identity : is_identity T op id
  associativity : associative T op

def M : Monoid := {
  T := Nat,
  id := 0,
  op := Nat.add,
  identity := sorry,
  associativity := sorry,
}

def id_preserving (M1 M2 : Monoid) (f: M1.T -> M2.T) : Prop :=
  f M1.id = M2.id

def op_preserving (M1 M2 : Monoid) (f: M1.T -> M2.T) : Prop :=
  ∀ a b : M1.T, f (M1.op a b) = M2.op (f a) (f b)

def morphism (M1 M2 : Monoid) (f: M1.T -> M2.T) : Prop :=
  (id_preserving M1 M2 f) ∧ (op_preserving M1 M2 f)

def identity_morphism (M: Monoid) : (M.T -> M.T) :=
  sorry

theorem identity_morphism_is_a_morphism: Prop :=
  ∀ M: Monoid, morphism M M (identity_morphism M)

def homomorphic (M1 M2 : Monoid) : Prop :=
  ∃ f: M1.T -> M2.T, morphism M1 M2 f

theorem every_monoid_is_homomorphic_to_itself (M: Monoid) : homomorphic M M :=
  sorry

/-
def isomorphic (M1 M2 : Monoid) : Prop :=
  ∃ f: M1.T -> M2.T, ∃ g: M2.T -> M1.T, (morphism )(f |> g = identity_morphism M1) ∧ (g |> f = identity_morphism M2)
-/

structure MonoidMorphism where
  M1 : Monoid
  M2 : Monoid
  f: M1.T -> M2.T
  is_id_preserving : id_preserving M1 M2 f
  is_op_preserving : op_preserving M1 M2 f

def identity_morphism_struct (M : Monoid) : MonoidMorphism := {
  M1 := M,
  M2 := M,
  f := (λ x => x),
  is_id_preserving := rfl,
  is_op_preserving := sorry
}

structure MonoidMorphism2 (M1 M2: Monoid) where
  f: M1.T -> M2.T
  is_id_preserving : id_preserving M1 M2 f
  is_op_preserving : op_preserving M1 M2 f


/-
def isomorphic (M1 M2 : Monoid) : Prop :=
  ∃ f: MonoidMorphism, ∃ g: MonoidMorphism, (morphism )(f |> g = identity_morphism M1) ∧ (g |> f = identity_morphism M2)
-/

/-
structure Cat where
  ob: Type
  hom: ob -> ob -> Type
  compose: ∀ a b c : ob, ∀ f : hom a b, ∀ g : hom b c, ∃ h : hom a c, (f |> g) = h
  associativity: ∀ a b c d : ob, ∀ f : hom a b, ∀ g : hom b c, ∀ h : hom c d, (f |> g) |> h = f |> (g |> h)
  identity: ∀ a : ob, ∃ f : hom a a, ∀ b : ob, (∀ g : hom a b, f |> g = g) ∧ (∀ g : hom b a, g |> f = g)
-/
