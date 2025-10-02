/-
Formalizing logic puzzles

https://en.wikipedia.org/wiki/Knights_and_Knaves

You come across three strangers, A, B, and C, each of whom is either a knight, who always tells the truth, or a knave, who always lies.

You ask A whether they are a knight or a knave, but do not hear their reply.
Then B says "A said they are a knave!"
Then C says "Don't believe B, they are lying!"

To solve the puzzle, note that no stranger can say they are a knave.
Therefore, B's statement is false, so they are a knave, making C's statement true, so they are a knight.
Since A would always claim to be a knight, it cannot be determined if they are a knight or a knave.
-/

axiom Stranger: Type

def knight: Stranger → Bool := sorry

def knave: Stranger → Bool := fun x => ¬ knight x

def reply (x: Stranger) (y: Prop): Prop := if knight x then y else ¬ y

theorem main (A B C: Stranger)
  (h1: reply B (reply A (knave A))) /- B's claim that A claimed to be a knave -/
  (h2: reply C (knave B)): /- C's claim that B is a knave -/
  (knave B) ∧ (knight C) := /- we wish to prove B is a knave and C is a knight -/
    sorry
