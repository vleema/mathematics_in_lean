import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    exact inf_le_right
    exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · repeat
      apply le_inf
      exact le_trans inf_le_left inf_le_left
    apply le_inf
    exact le_trans inf_le_left inf_le_right
    exact le_trans inf_le_right le_rfl
  · repeat
      apply le_inf
    exact inf_le_left
    exact le_trans inf_le_right inf_le_left
    exact le_trans inf_le_right inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    exact le_sup_right
    exact le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  exact sup_assoc x y z -- Just demonstrated with inf! >:}

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · exact inf_le_left
  · apply le_inf
    · rfl
    · exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · rfl
    · exact inf_le_left
  · exact le_sup_left

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply symm
  calc
    (a ⊔ b) ⊓ (a ⊔ c)
      = ((a ⊔ b) ⊓ a) ⊔ ((a ⊔ b) ⊓ c) := by rw [h]
    _ = a ⊔ ((a ⊔ b) ⊓ c)             := by rw [inf_comm, absorb1]
    _ = a ⊔ (c ⊓ (a ⊔ b))             := by rw [inf_comm]
    _ = a ⊔ ((c ⊓ a) ⊔ (c ⊓ b))       := by rw [h]
    _ = (a ⊔ (c ⊓ a)) ⊔ (c ⊓ b)       := by rw [sup_assoc]
    _ = a ⊔ (b ⊓ c)                   := by rw [inf_comm, absorb2, inf_comm]

#check (x ⊓ y) ⊔ (x ⊓ z)
#check a ⊔ (b ⊓ c)
#check (a ⊓ (a ⊔ b)) ⊔ (c ⊓ (a ⊔ b))
#check a ⊔ ((a ⊔ b) ⊓ c)

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply symm
  calc
    (a ⊓ b) ⊔ (a ⊓ c)
      = ((a ⊓ b) ⊔ a) ⊓ ((a ⊓ b) ⊔ c) := by rw [h]
    _ = a ⊓ ((a ⊓ b) ⊔ c)             := by rw [sup_comm, absorb2]
    _ = a ⊓ (c ⊔ (a ⊓ b))             := by rw [sup_comm]
    _ = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b))       := by rw [h]
    _ = (a ⊓ (c ⊔ a)) ⊓ (c ⊔ b)       := by rw [inf_assoc]
    _ = a ⊓ (b ⊔ c)                   := by rw [sup_comm, absorb1, sup_comm]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  simpa [add_le_add_left] using h

example (h: 0 ≤ b - a) : a ≤ b := by
  simpa [add_le_add_left] using h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₁ : 0 ≤ (b - a) * c := mul_nonneg (sub_nonneg_of_le h) h'
  rw [sub_mul] at h₁
  exact sub_nonneg.mp h₁

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h₁ : 0 ≤ dist x y + dist y x := by rw [← dist_self x] ; exact dist_triangle x y x
  rw [dist_comm y x] at h₁
  linarith

end

#check div_le_iff_le_mul
