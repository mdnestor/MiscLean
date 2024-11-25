
-- This file shows every strategy profile in a zero-sum game is Pareto-optimal.

-- prelude

-- the type of relations on a type
def Rel (X: Type): Type :=
  X → X → Prop

-- transitivity and irreflexivity

def Rel.trans (R: Rel X): Prop :=
  ∀ x x' x'', R x x' → R x' x'' → R x x''

def Rel.irrefl (R: Rel X): Prop :=
  ∀ x, ¬ R x x

-- Definition of game: a set of players and a set of strategies, and each player has a preference relation on the strategies of others.

structure Game where
  player: Type
  strategy: Type
  pref: player → Rel (player → strategy)

-- Alternate definiton: a game with player set `P` and strategy set `S` is just `P → Rel (P → S)`.
-- It feels weird to call this a game so let's call it "Pref".

def Pref (P S: Type): Type :=
  P → Rel (P → S)

/-

some definitions:

1. a strategy profile π' is called a "Pareto improvement" over π if every player prefers π' over π.

2. a strategy profile π is Pareto-optimal if there exists no strict Pareto improvement.

3. a zero sum game is one in which if player i strictly prefers π' over π, then player j strictly prefers π over π'.

-/

def pareto_improvement (pref: Pref P S): Rel (P → S) :=
  fun π π' => ∀ i, pref i π π'

def pareto_optimal (pref: Pref P S) (π: P → S): Prop :=
  ∀ π', ¬ pareto_improvement pref π π'

def zero_sum (pref: Pref P S): Prop :=
  ∀ i j π π', i ≠ j → pref i π π' → pref j π' π

/-

theorem: in a **zero-sum** game with at least 2 players, if every player's preference is transitive and irreflexive, then every strategy profile is Pareto-optimal.

proof:

1. let π be a strategy profile, and suppose for contradiction there exists a Pareto improvement π' over π.
2. let i, j be two distinct players. From (1), i and j both prefer π' over π.
3. by definition of zero-sum, since i prefers π' over π by (2) then j prefers π over π'.
4. combining (2) and (3) by transitivity, j prefers π to itself, contradicting irreflexivity.

-/

theorem zero_sum_pareto_optimal (pref: Pref P S) (i j: P) (h0: i ≠ j) (h1: zero_sum pref) (h2: ∀ i, Rel.irrefl (pref i)) (h3: ∀ i, Rel.trans (pref i)): ∀ π, pareto_optimal pref π := by
  intro π π' h
  have h4 := h1 i j π π' h0 (h i)
  have h5 := h3 j π π' π (h j) h4
  exact h2 j π h5
