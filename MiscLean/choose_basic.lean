/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

import Mathlib.Data.Nat.Choose.Basic

example (n: Nat): Nat.choose n 0 = 1 := Nat.choose_zero_right n

example (n: Nat): Nat.choose n n = 1 := Nat.choose_self n

example (n k: Nat) (h: k ≤ n): Nat.choose n k = Nat.choose n (n - k) := Eq.symm (Nat.choose_symm h)
