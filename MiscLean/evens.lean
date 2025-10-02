/-
Some easy theorems about even numbers:
- the sum of two even numbers is even
- the product of two even numbers is even
- a number is even iff. its square is even
Makes generous use of calculational proofs, i.e. the `calc` tactic.
-/

-- definition of even
def even (n: Nat): Prop :=
  ∃ k: Nat, 2 * k = n

-- theorem: a number is not even iff. it can be written as 2*k + 1
theorem odd (n: Nat): (∃ k: Nat, n = 2*k + 1) ↔ ¬(even n) := by
  sorry

-- if m and n are both even then m + n is even
theorem sum_of_even_is_even (m n: Nat) (h0: even m) (h1: even n): even (m + n) := by
  obtain ⟨k0, h2⟩ := h0
  obtain ⟨k1, h3⟩ := h1
  exists k0 + k1
  calc
    2 * (k0 + k1) = 2 * k0 + 2 * k1 := by rw [Nat.left_distrib]
                _ = m + n           := by rw [h2, h3]

-- if m and n are both even then m*n is even
theorem product_of_even_is_even (m n: Nat) (h0: even m) (h1: even n): even (m * n) := by
  obtain ⟨k0, h2⟩ := h0
  obtain ⟨k1, h3⟩ := h1
  exists 2 * k0 * k1
  calc
    2 * (2 * k0 * k1) = 2 * (k0 * 2 * k1)   := by rw [Nat.mul_comm 2 k0]
                    _ = (2 * k0) * (2 * k1) := by repeat rw [Nat.mul_assoc]
                    _ = m * n               := by rw [h2, h3]

theorem contrapositive (P Q: Prop): P → Q ↔ (¬ Q → ¬ P) := by
  apply Iff.intro
  exact mt -- modus tollens
  intro h p
  exact Classical.not_not.mp (mt h (not_not_intro p))

-- n is even if and only if n^2 is even
theorem even_iff_square_even (n: Nat): even n ↔ even (n^2) := by
  apply Iff.intro
  -- forward
  intro h0
  obtain ⟨k, h1⟩ := h0
  exists 2 * k^2
  calc
    2 * (2 * k ^ 2) = 2 * (2 * (k * k)) := by rw [Nat.pow_two]
                  _ = 2 * (2 * k * k)   := by rw [Nat.mul_assoc]
                  _ = 2 * (k * 2 * k)   := by rw [Nat.mul_comm 2 k]
                  _ = (2 * k) * (2 * k) := by repeat rw [Nat.mul_assoc]
                  _ = n * n             := by rw [h1]
                  _ = n^2               := by rw [Nat.pow_two]
  -- reverse
  rw [contrapositive]
  intro h0
  have h1 := Iff.mpr (odd n) h0
  obtain ⟨k, h2⟩ := h1
  have h3 := calc
      n^2 = n * n                             := by rw [Nat.pow_two]
        _ = (2 * k + 1) * (2 * k + 1)         := by rw [h2]
        _ = 2 * (k * (2 * k + 1)) + 2 * k + 1 := by rw [Nat.right_distrib, Nat.one_mul, Nat.add_assoc, Nat.mul_assoc]
        _ = 2 * (k * (2 * k + 1) + k) + 1     := by rw [←Nat.left_distrib]
  have h4 := Iff.mp (odd (n^2))
  have h5 : ∃ k, n^2 = 2 * k + 1 := by
    exists k * (2 * k + 1) + k
  exact h4 h5
