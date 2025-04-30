import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_comm, add_comm a b]
  rw [neg_add_cancel_left b a]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [add_comm a c] at h
  calc
    b = b + 0          := by rw [add_zero]
    _ = b + (a + -a)   := by rw [← add_neg_cancel a]
    _ = (b + a) + -a   := by rw [← add_assoc b a]
    _ = (a + b) + -a   := by rw [add_comm b a]
    _ = (c + a) + -a   := by rw [h]
    _ = c              := by rw [add_neg_cancel_right]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [add_comm a b, add_comm c b] at h
  exact add_left_cancel h

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a =  0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  exact add_left_cancel h


theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  calc
    -a = -a + 0       := by rw [add_zero]
     _ = -a + (a + b) := by rw [h]
     _ = b            := by rw [neg_add_cancel_left]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [add_comm] at h
  have h1 : -b = a := neg_eq_of_add_eq_zero h
  exact symm h1

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  exact InvolutiveNeg.neg_neg a

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg a a]
  exact add_neg_cancel a


theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  exact _root_.two_mul a

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  calc
    a * a⁻¹
      = 1 * (a * a⁻¹)               := symm (one_mul (a * a⁻¹))
    _ = (a⁻¹)⁻¹ * a⁻¹ * (a * a⁻¹)   := by rw [inv_mul_cancel a⁻¹]
    _ = (a⁻¹)⁻¹ * ((a⁻¹ * a) * a⁻¹) := by rw [mul_assoc, ← mul_assoc a⁻¹ a a⁻¹]
    _ = (a⁻¹)⁻¹ * (1 * a⁻¹)         := by rw [inv_mul_cancel]
    _ = (a⁻¹)⁻¹ * a⁻¹               := by rw [one_mul]
    _ = 1                           := by rw [inv_mul_cancel]

theorem mul_one (a : G) : a * 1 = a := by
  calc
    a * 1
      = a * (a⁻¹ * a) := by rw [← inv_mul_cancel a]
    _ = (a * a⁻¹) * a := by rw [mul_assoc]
    _ = 1 * a         := by rw [mul_inv_cancel]
    _ = a             := by rw [one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply symm
  calc
    b⁻¹ * a⁻¹
      = (b⁻¹ * a⁻¹) * 1                     := by rw [mul_one]
    _ = (b⁻¹ * a⁻¹) * (a * b * (a * b)⁻¹)   := by rw [← mul_inv_cancel]
    _ = b⁻¹ * (a⁻¹ * (a * b * (a * b)⁻¹))   := by rw [mul_assoc]
    _ = b⁻¹ * ((a⁻¹ * (a * b)) * (a * b)⁻¹) := by rw [← mul_assoc a⁻¹]
    _ = b⁻¹ * ((a⁻¹ * a) * b * (a * b)⁻¹)   := by rw [← mul_assoc a⁻¹]
    _ = b⁻¹ * (1 * b * (a * b)⁻¹)           := by rw [inv_mul_cancel]
    _ = b⁻¹ * (b * (a * b)⁻¹)               := by rw [one_mul]
    _ = (b⁻¹ * b) * (a * b)⁻¹               := by rw [← mul_assoc b⁻¹]
    _ = 1 * (a * b)⁻¹                       := by rw [inv_mul_cancel]
    _ = (a * b)⁻¹                           := by rw [one_mul]

end MyGroup

end
