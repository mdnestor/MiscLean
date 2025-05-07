
import Mathlib.NumberTheory.Divisors

theorem reciprocal_divisor {n d: Nat} (h: d ∈ n.divisors): (n / d) ∈ n.divisors := by
  simp_all [Nat.divisors]
  repeat constructor
  . apply (Nat.one_le_div_iff h.left.left).mpr
    exact Nat.le_of_lt_succ h.left.right
  . calc
      n / d ≤ n := by exact Nat.div_le_self n d
      _ < n + 1 := by exact lt_add_one n
  . exact Nat.div_dvd_of_dvd h.right

def divisor_involution (n: Nat): n.divisors → n.divisors :=
  fun ⟨d, hd⟩ => ⟨n / d, reciprocal_divisor hd⟩

example (n: Nat): Function.Bijective (divisor_involution n) := by
  constructor
  . intro ⟨d1, hd1⟩ ⟨d2, hd2⟩ h
    simp_all [divisor_involution]
    simp_all [Nat.divisors]
    have: (n / d1) * d1 = (n / d2) * d1 := by exact congrFun (congrArg HMul.hMul h) d1
    have: (n / d1) * d1 * d2 = (n / d2) * d1 * d2 := by aesop
    rw [Nat.div_mul_cancel hd1.2] at this
    rw [Nat.mul_assoc, Nat.mul_comm d1, ←Nat.mul_assoc] at this
    rw [Nat.div_mul_cancel hd2.2] at this
    apply @Nat.mul_left_cancel n
    calc
      0 < 1 := by exact Nat.one_pos
      _ ≤ d1 := by exact hd1.1.1
      _ ≤ n := by exact Nat.le_of_lt_succ hd1.1.2
    apply Eq.symm
    exact this
  . intro ⟨d, hd⟩
    exists divisor_involution n ⟨d, hd⟩
    simp [divisor_involution]
    apply @Nat.mul_right_cancel (n / (n / d)) (n / d)
    simp [Nat.divisors] at hd
    apply Nat.add_one_le_iff.mp
    have: 0 < d := by aesop
    apply (Nat.one_le_div_iff this).mpr
    exact Nat.le_of_lt_succ hd.1.2
    simp [Nat.divisors] at hd
    rw [Nat.mul_comm d, Nat.div_mul_cancel hd.2, Nat.div_mul_cancel (Nat.div_dvd_of_dvd hd.2)]
