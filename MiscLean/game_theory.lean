
set_option linter.unusedSectionVars false

/-

Game theory is fundamentally based on *order theory*
because games model interactions between *agents*
which have *preferences* about the state of world.

So the first definition is that of a preference, which is simply a relation on a set.
Sometimes "preference relations" are required to be transitive and/or irreflexive (i.e. strict).
A reflexive preference is called "weak" and an irreflexive preference is called "strong".

-/

def Relation (X Y: Type): Type :=
  X → Y → Prop

def Prefer (X: Type): Type :=
  Relation X X

def reflexive {X: Type} (prefer: Prefer X): Prop :=
  ∀ x, prefer x x

def irreflexive {X: Type} (prefer: Prefer X): Prop :=
  ∀ x, ¬ prefer x x

def transitive {X: Type} (prefer: Prefer X): Prop :=
  ∀ x y z, prefer x y → prefer y z → prefer x z

def antisymmetric {X: Type} (prefer:  Prefer X): Prop :=
  ∀ x y, prefer x y → prefer y x → x = y

/-

First definition of a normal-form game based on the notion of utility, consisting of:

- a set of players,
- a set of strategies (assumed to be the same for all players),
- a set of possible 'utility' values,
- a 'play' function which maps strategy profiles to utility profiles, where
  - a 'strategy profile' is a choice of strategy for each player,
  - a 'utility profile' is an assignment of utilities to each player; and
- a preference relation on utility values, assumed to be shared by all players.

For example the utility could be a numerical value
and all players agree "more is better" (for themselves).

Note the 'play' function wraps what is usually called the 'payoff matrix'.

-/

class UtilityGame where
  player  : Type
  strategy: Type
  utility : Type
  play: (player → strategy) → (player → utility)
  prefer: Prefer utility

-- A generalization: instead of each player getting a utility,
-- the game has some 'outcome' and the players have a preference on outcomes.

class OutcomeGame where
  player  : Type
  strategy: Type
  outcome : Type
  play: (player → strategy) → outcome
  prefer:  player → Prefer outcome

-- Every utility game is an outcome game where the outcomes are utility assignments
-- and players prefer outcomes where they get higher utility.

def UtilityGame.toOutcomeGame (game: UtilityGame): OutcomeGame := {
  player   := player
  strategy := strategy
  outcome  := player → utility
  play     := play
  prefer := fun p => fun π0 π1 =>
    let u0 := π0 p -- the utility he gets from the first outcome
    let u1 := π1 p -- the utility he gets from the second outcome
    prefer u0 u1 -- he prefers the second profile iff. u0 ≤ u1
}

-- One more further disillation: we don't need to explicitly reference the set of outcomes.
-- Instead, the players can have preferences directly on strategy profiles.

class Game where
  player  : Type
  strategy: Type
  prefer: player → Prefer (player → strategy)

-- This is actually an equivalent representation because we can treat the strategy profiles themselves as outcomes.

def OutcomeGame.toGame (game: OutcomeGame): Game := {
  player   := player
  strategy := strategy
  prefer := fun p => fun π0 π1 => prefer p (play π0) (play π1)
}

def Game.toOutcomeGame (game: Game): OutcomeGame := {
  player   := player
  strategy := strategy
  outcome  := player → strategy
  play     := id
  prefer   := prefer
}



-- For the remainder, assume a game is fixed (and for technicality that its type of players has decidable equality).

variable {game: Game} [DecidableEq game.player]

open Game

-- To define concepts like dominant strategies and best response, we will frequently use the following helper:
-- given a function f: X → Y and a pair (x0, y0) we can "update" f to take the value f(x0) = y0.

def update {X Y: Type} [DecidableEq X] (f: X → Y) (x0: X) (y0: Y): X → Y :=
  fun x => if x = x0 then y0 else f x

-- Given a fixed strategy profile, a strategy is called a player's 'best response'
-- if no other strategy is better in that profile.

def best_response (π: player → strategy) (p: player) (s: strategy): Prop :=
  ∀ s', prefer p (update π p s') (update π p s)

-- A Nash equilibrium is a profile in which every player is using their best response.

def nash_equilibrium (π: player → strategy): Prop :=
  ∀ p, best_response π p (π p)

-- For a fixed player, a strategy s 'dominates' another strategy s0 if it's always preferable to play s over s0.
-- The strategy s is called 'dominant' if it dominates all other strategies.

def dominates (p: player) (s0 s: strategy): Prop :=
  ∀ π, prefer p (update π p s0) (update π p s)

def dominant (p: player) (s: strategy): Prop :=
  ∀ s0, dominates p s0 s

-- Some immediately obvious theorems:
-- A strategy is dominant iff. it is the best response to every profile (this is basically just by definition).

theorem dominant_iff_best_response (p: player) (s: strategy): dominant p s ↔ ∀ π, best_response π p s := by
  exact forall_comm

-- Any profile where every player is using a dominant strategy is a Nash equilibrium.

theorem dominant_equilibrium (π: player → strategy) (h: ∀ p, dominant p (π p)): nash_equilibrium π := by
  intro p s
  exact h p s π

/-

Example: prisoner's dilemma.

It is a utility game with
- two players
- two strategies, defect or not
- four possible scores / utilities - sometimes described as costs / negative utilities, e.g. prison sentences

We can model the players as {0, 1} and the strategies as {false, true} with true = defect,
and the payoffs as 0, 1, 2, 3. Maybe 0 = death, 1 = prison, 2 = probation, and 3 = freedom.
Here is the payoff matrix (i.e. the play function) with (u0, u1) the utilities of players 0 and 1 respectively:

                           Player 1
                     cooperate   defect
                    --------------------
          cooperate | (2, 2)  |  (0, 3)
Player 0            |-------------------
          defect    | (3, 0)  |  (1, 1)

-/

def PrisonerDilemma: UtilityGame := {
  player   := Fin 2
  strategy := Bool
  utility  := Fin 4
  play := fun π => fun p => match (π 0, π 1) with
    -- neither defect
    | (false, false) => match p with
      | 0 => 2
      | 1 => 2
    -- first defects
    | (true, false) => match p with
      | 0 => 3
      | 1 => 0
    -- second defects
    | (false, true) => match p with
      | 0 => 0
      | 1 => 3
    -- both defect
    | (true, true) => match p with
      | 0 => 1
      | 1 => 1
  prefer := fun u1 u2 => u1 ≤ u2
}

instance: DecidableEq PrisonerDilemma.toOutcomeGame.toGame.player :=
  instDecidableEqFin 2

-- In the prisoner's dilemma, the Nash equilibrium is for both to defect.

example: @nash_equilibrium PrisonerDilemma.toOutcomeGame.toGame _ (fun _ => true) := by
  intro p s
  simp [PrisonerDilemma, UtilityGame.toOutcomeGame, OutcomeGame.toGame, update]
  change Fin 2 at p
  change Bool at s
  match p with
  | 0 => cases s <;> simp
  | 1 => cases s <;> simp



-- Given a preference, there is the associated "strict" preference
-- and all the associated notions

def strict {X: Type} (prefer:  Prefer X): Prefer X :=
  fun x1 x2 => prefer x1 x2 ∧ ¬ prefer x2 x1

def strict_best_response (π: player → strategy) (p: player) (s: strategy): Prop :=
  ∀ s', s ≠ s' → strict (prefer p) (update π p s') (update π p s)

def strict_nash_equilibrium (π: player → strategy): Prop :=
  ∀ p, best_response π p (π p)

def strict_dominates (p: player) (s0 s: strategy): Prop :=
  ∀ π, strict (prefer p) (update π p s0) (update π p s)

def strict_dominant (p: player) (s: strategy): Prop :=
  ∀ s0, strict_dominates p s0 s

-- When strict best response / Nash equilibria / dominant strategies exist, they are unique.

theorem strict_best_response_unique (π: player → strategy) (p: player) (s s': strategy) (h1: strict_best_response π p s) (h2: strict_best_response π p s'): s = s' := by
  sorry

theorem strict_nash_equilibrium_unique (π π': player → strategy) (h1: strict_nash_equilibrium π) (h2: strict_nash_equilibrium π'): π = π' := by
  sorry

theorem strict_dominant_unique (p: player) (s s': strategy) (h1: strict_dominant p s) (h2: strict_dominant p s'): s = s' := by
  sorry



-- Given an indexed collection P_1, P_2, ..., P_n of individual preferences on X,
-- the Pareto preference is defined by x ≤ y iff. every individual prefers x ≤ y.

def pareto {X I: Type} (prefer:  I → Prefer X): Prefer X :=
  fun x1 x2 => ∀ i, prefer i x1 x2

-- A profile π1 Pareto dominates π0 if every player prefers π1.
-- It is Pareto dominant if it Pareto dominates every other strategy.
-- Likewise for strict Pareto dominates.

def pareto_dominates (π0 π1: player → strategy): Prop :=
  pareto prefer π0 π1

def pareto_dominant (π: player → strategy): Prop :=
  ∀ π0, pareto_dominates π0 π

def strict_pareto_dominates (π0 π1: player → strategy): Prop :=
  strict (pareto prefer) π0 π1

def strict_pareto_dominant (π: player → strategy): Prop :=
  ∀ π0, strict_pareto_dominates π0 π

-- π1 strictly Pareto dominates π0 iff. everyone weakly prefer π1, and someone strongly prefers π1.

theorem strict_pareto_dominates_iff (π0 π1: player → strategy): strict_pareto_dominates π0 π1 ↔ (∀ p, prefer p π0 π1) ∧ (∃ p, ¬ prefer p π1 π0) := by
  simp [strict_pareto_dominates]
  constructor
  · intro h
    constructor
    · exact h.1
    · have := h.2
      simp [pareto] at this
      exact this
  · intro h
    constructor
    · intro i
      exact h.1 i
    · simp [pareto]
      exact h.2

-- A profile is Pareto efficient if it is not strictly Pareto dominated.

def pareto_efficient (π: player → strategy): Prop :=
  ∀ π1, ¬ strict_pareto_dominates π π1

-- A zero-sum game is one where preferences are flipped between different players.

def zero_sum (game: Game): Prop :=
  ∀ p1 p2 π1 π2, p1 ≠ p2 → (prefer p1 π1 π2 ↔ prefer p2 π2 π1)

/-

In a zero-sum game with at least 2 players and all preferences reflexive and anti-symmetric,
every strategy profile is Pareto efficient.

Proof:
- Suppose for contradiction π is not Pareto efficient.
- Then there exists strict Pareto improvement π'.
- So any two distinct players p1, p2 weakly prefer π ≤ π'.
- By zero sum, since p1 weakly prefers π ≤ π' then p2 weakly prefers π' ≤ π.
- By reflexivity π = π'.
- But since π' is a strict improvement, some player p3 strictly prefers π < π' = π, contradiction.

-/

theorem zero_sum_pareto_efficient (h1: zero_sum game) (h2: ∀ p, reflexive (prefer p)) (h3: ∀ p, antisymmetric (prefer p)) (h4: ∀ p: player, ∃ p': player, p ≠ p'): ∀ π: player → strategy, pareto_efficient π := by
  intro π π' h_strict
  simp_all [strict_pareto_dominates, strict, pareto]
  obtain ⟨p1, p1_not_pref_π⟩ := h_strict.2
  obtain ⟨p2, p1_neq_p2⟩ := h4 p1
  have p1_pref_π' := h_strict.1 p1
  have p2_pref_π' := h_strict.1 p2
  have p2_pref_π := (h1 _ _ π π' p1_neq_p2).mp p1_pref_π'
  have π_eq_π' := h3 p2 _ _ p2_pref_π' p2_pref_π
  rw [π_eq_π'] at p1_not_pref_π
  exact p1_not_pref_π (h2 p1 π')
