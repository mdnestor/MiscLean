def prime (n: Nat): Prop :=
  n > 1 ∧ ∀ d: Nat, n % d = 0 → d = 1 ∨ d = n

def prime_check (n: Nat): Bool := by
  let range := List.range (n + 1)
  let divisors := List.filter (fun d => n % d = 0) range
  let is_prime := decide (divisors.length = 2)
  exact is_prime

example (n: Nat): prime n ↔ (prime_check n = true) := by
  apply Iff.intro
  intro h1
  simp [prime_check]
  sorry
  intro h1
  simp [prime_check] at h1
  apply And.intro
  sorry
  intro d h2
  sorry
