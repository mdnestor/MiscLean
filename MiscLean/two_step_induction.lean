/-
We define a function recursively for all positive integers $n$ by $f(1)=1$, $f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$. Show that $f(n)=$ $2^{n}+(-1)^{n}$, using the second principle of mathematical induction.
-/
import Mathlib

def f: Nat → Nat
| 0 => 2
| 1 => 1
| n + 2 => f (n + 1) + 2 * f (n)

example (n: Nat): f n = 2^n + (-1: Int)^n := by
  apply @Nat.strong_induction_on (fun n => f n = 2^n + (-1: Int)^n)
  intro m h
  match m with
  | 0 => rfl
  | 1 => rfl
  | p + 2 =>
    simp [f, h p (by simp), h (p + 1) (by simp)]
    ring_nf
