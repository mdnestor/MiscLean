
-- formalization of "L-system" https://en.wikipedia.org/wiki/L-system

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Group.Action.Defs

variable {X: Type u}

-- turns out to be pretty simple, just the lift of a map X → List X
def LSystem (p: X → List X): List X → List X :=
  List.join ∘ List.map p

-- the Fibonacci L-system
def pf: Bool → List Bool :=
  fun x => match x with
  | true => [true, false]
  | false => [true]

-- in order to define the Fibonacci word, need to define the property of an L-system stabilizing
-- i.e., if a is the initial word then the sequence "converges" to the infinite word w

-- maybe use the concept of a morphic word?

-- suppose `f: X → List X`
-- and suppose the symbol `a` satisfies `f a = [a] ++ s`
-- then given `L f : List X → List X`
-- you have the sequence `(L f) [a] = [a, s]`
-- then `(L^[2] f) [a] = [a, s] ++ (f s)`
-- then `(L^[3] f) [a] = [a] ++ (f s) ++ (f f s)`
-- or somethingg

def append_list_seq (L: List X) (a: Nat → X): Nat → X := fun n =>
  if h : n < L.length then L.get ⟨n, h⟩ else a (n - L.length)

def join_seq {α} (a : Nat → List α) (ha : ∀ n, a n ≠ []) (n : Nat) : α :=
  if h: n < (a 0).length then
    (a 0).get ⟨n, h⟩
  else
    have : (a 0).length ≠ 0 := by simp [ha]
    have : 0 < n := by omega
    join_seq (fun n => a (n + 1)) (fun n => ha _) (n - (a 0).length)

theorem join_seq_eq (a: Nat → List X) (h: (n: Nat) → a n ≠ []):
  join_seq a h = append_list_seq (a 0) (join_seq (fun n => a (n + 1)) (fun n => h (n + 1))) := by
  ext
  simp [append_list_seq]
  rw [join_seq]
  simp

def fixed_point (f: X → X) (x: X): Prop := f x = x

def lift (f: X → List X) (h: ∀ x, f x ≠ []): (Nat → X) → (Nat → X) := by
  intro a
  exact join_seq (f ∘ a) sorry

def morphic_word (f: X → List X) (a: X) (s: List X) (hS: Nonempty S) (h: f a = [a] ++ s):
  fixed_point (lift f sorry) (append_list_seq [a] (join_seq (fun n => (List.join ∘ List.map f)^[n] s) sorry)) := sorry

-- notice the term `List.join ∘ List.map f` appears in the definition of a morphic word

-- side note: it's interesting that `append_list_seq` is a monoid action

instance: Monoid (List X) := {
  mul := List.append
  mul_assoc := List.append_assoc
  one := List.nil
  one_mul := List.nil_append
  mul_one := List.append_nil
}

instance: MulAction (List X) (Nat → X) := {
  smul := append_list_seq
  one_smul := by intro; rfl
  mul_smul := by sorry -- ??
}

-- the other strategy is like..
-- suppose that for a given axiom a, its always the case that p^[n](a) is a proper subword of p^[n+1](a)
-- then you should be able to construct the infinite word it "converges" to

def bounded (a: Nat → Nat): Prop :=
  ∃ b: Nat, ∀ n: Nat, a n ≤ b

theorem unbounded_if (a: Nat → Nat) (h: ∀ n: Nat, a n < a (n + 1)): ¬ bounded a := sorry

noncomputable def collapse_proper_ascending_sentence (S: Nat → (List X))
  (h1: ∀ n: Nat, (S n).length < (S (n + 1)).length)
  (h2: ∀ n: Nat, List.take (S n).length (S (n + 1)) = S n): Nat → X := by
  intro n
  have := unbounded_if (fun n: Nat => (S n).length) sorry
  simp [bounded] at this
  specialize this n
  let i: Nat := sorry
  have: n < (S i).length:= sorry
  
  exact List.get (S n) (Fin.mk n sorry)

def Sf: Nat → List Bool := fun n => (LSystem pf)^[n] [false]

theorem hf1: ∀ n: Nat, (Sf n).length < (Sf (n + 1)).length := by
  intros
  simp [Sf]
  simp [LSystem, pf]
  sorry

theorem hf2: ∀ n: Nat, List.take (Sf n).length (Sf (n + 1)) = Sf n := by
  intros
  simp [Sf]
  simp [LSystem, pf]
  sorry

noncomputable def fibword: Nat → Bool := collapse_proper_ascending_sentence Sf hf1 hf2
