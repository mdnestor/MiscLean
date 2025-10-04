
/-
A simplified Eckmann-Hilton argument (exercise 1.1.14 in "Intro. to Categorical Logic" by Awodey & Bauer, https://awodey.github.io/catlog/notes/catlogdraft.pdf)

Suppose m1, m2 are two binary operations on a common set, such that they
- share a common unit e,
- satisfy the "swap-commute" condition, m1(m2(x,y),m2(z,w)) = m2(m1(x,z),m1(y,w)).

Then m1 and m2 are:
- equal (m1 = m2)
- associative
- commutative

-/

variable {X: Type}

def Assoc (m: X → X → X): Prop :=
  ∀ x y z, m (m x y) z = m x (m y z)

def Comm (m: X → X → X): Prop :=
  ∀ x y, m x y = m y x

def IsUnit (m: X → X → X) (e: X): Prop :=
  ∀ x, m e x = x ∧ m x e = x

def SwapCommute (m1 m2: X → X → X): Prop :=
  ∀ x y z w, m1 (m2 x y) (m2 z w) = m2 (m1 x z) (m1 y w)

/-

Suppose m1, m2 are two binary operations on a common set, such that they

- share a common unit e,
- satisfy the "swap-commute" condition, m1(m2(x,y),m2(z,w)) = m2(m1(x,z),m1(y,w)).

Then m1 and m2 are

- equal (m1 = m2),
- associative,
- commutative.

-/

example {m1 m2: X → X → X} {e: X} (h1: IsUnit m1 e) (h2: IsUnit m2 e) (h3: SwapCommute m1 m2): m1 = m2 := by
  ext x y
  rw [←(h2 x).right, ←(h2 y).left]
  rw [h3]
  rw [(h1 x).right, (h1 y).left]
  rw [(h2 x).right, (h2 y).left]

example {m: X → X → X} {e: X} (h1: IsUnit m e) (h2: SwapCommute m m): Assoc m := by
  intro x y z
  rw [←(h1 z).left]
  rw [h2]
  rw [(h1 x).right]
  rw [(h1 z).left]

example {m: X → X → X} {e: X} (h1: IsUnit m e) (h2: SwapCommute m m): Comm m := by
  intro x y
  rw [←(h1 x).left, ←(h1 y).right]
  rw [h2]
  rw [(h1 y).left, (h1 x).right]
  rw [(h1 x).left, (h1 y).right]
