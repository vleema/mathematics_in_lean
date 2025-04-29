import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    exact le_trans (min_le_left (min a b) c) (min_le_left a b)
    apply le_min
    exact le_trans (min_le_left (min a b) c) (min_le_right a b)
    apply le_trans (min_le_right (min a b) c)
    rfl
  · apply le_min
    apply le_min
    exact le_trans (min_le_left a (min b c)) (le_rfl)
    exact le_trans (min_le_right a (min b c)) (min_le_left b c)
    exact le_trans (min_le_right a (min b c)) (min_le_right b c)

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  have h : min a b ≤ a := min_le_left a b
  exact add_le_add_right h c
  rw [add_le_add_iff_right]
  exact min_le_right a b

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · exact aux a b c
  · rw [← add_neg_cancel_right (min (a + c) (b + c)) c]
    rw [add_assoc, add_comm, add_comm (min a b) c, add_assoc]
    rw [add_le_add_iff_left]
    apply le_min
    · conv => rhs ; rw [← add_neg_cancel_left c a] ; rw [← add_assoc]
      rw [add_comm c (-c), add_assoc]
      rw [add_le_add_iff_left, add_comm c a]
      exact min_le_left (a + c) (b + c)
    · conv => rhs ; rw [← add_neg_cancel_left c b] ; rw [← add_assoc]
      rw [add_comm c (-c), add_assoc]
      rw [add_le_add_iff_left, add_comm c b]
      exact min_le_right (a + c) (b + c)

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check add_sub_cancel_right
#check sub_add_cancel


example : |a| - |b| ≤ |a - b| := by
  simp
  conv => lhs ; rw [← sub_add_cancel a b]
  exact abs_add_le (a - b) b
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  repeat
    apply dvd_add
  · rw [← mul_assoc, mul_comm y x, mul_assoc, mul_comm]
    exact dvd_mul_left x (y * z)
  · rw [pow_two]
    exact dvd_mul_left x x
  · apply dvd_trans h
    rw [pow_two]
    exact dvd_mul_left w w

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  · apply dvd_gcd
    exact gcd_dvd_right m n
    exact gcd_dvd_left m n
  · apply dvd_gcd
    exact gcd_dvd_right n m
    exact gcd_dvd_left n m

end
