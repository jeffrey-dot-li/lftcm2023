import LftCM.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

theorem min_symm : min a b = min b a := by
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


theorem min_inv: min (a) (b) = -max (-a) (-b) := by
  -- simp
  if h₀ : a = b
  then
    rw [h₀,  min_self, max_self]
    ring
  else
    if h : a < b
    then
      rw [min_def, max_def]
      have h₂ : a <= b := by exact le_iff_eq_or_lt.mpr (Or.inr h)
      have h₃ : ¬(-a ≤ -b) := by simp [h]
      -- (-a > -b)
        -- have k:= by exact lt_iff_not_le.mp h
        -- have x := (neg_le b a).mpr
        -- have k₂ := by exact mt x k
      rw [if_pos h₂, if_neg (h₃)]
      ring
    else
      rw [min_def, max_def]
      have k : a >= b := by
        have k : ¬¬b ≤ a := by exact mt lt_iff_not_le.mpr h
        have k: b <= a := by exact not_not.mp k
        simp [k]
      have h₁: a > b := by exact lt_iff_le_and_ne.mpr ⟨k, Ne.symm h₀⟩
      have h₂ : ¬(a <= b) := by simp [h₁]
      have h₃ : (-a ≤ -b) := by
        have k := by exact le_iff_eq_or_lt.mpr (Or.inr h₁)
        simp [k]
      rw[if_neg h₂, if_pos h₃]
      ring




theorem neg (h: -a = -b): a = b := by
  rw [← neg_neg a, ← neg_neg b, h]

example : max a b = max b a := by
  apply neg
  rw[ ← neg_neg a, ← neg_neg b, ← min_inv, ← min_inv, min_symm]


example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    · apply le_min
      · apply le_trans
        apply min_le_left
        apply min_le_right
      · apply min_le_right
  · apply le_min
    · apply le_min
      · apply min_le_left
      · apply le_trans
        apply min_le_right
        apply min_le_left
    · apply le_trans
      apply min_le_right
      apply min_le_right


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_right
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]


#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  rw [←add_le_add_iff_right (|b|)]
  ring
  apply le_trans

  have h: |a| <= |b + (a - b)| := by
    ring
    apply le_refl
  apply h
  apply abs_add

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
  apply dvd_add
  · apply dvd_add
    · have h: y * (x*z) = x * (y*z) := by ring
      rw [h]
      apply dvd_mul_right
    · apply dvd_mul_left
  · apply dvd_mul_of_dvd_right
    apply h
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat'
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left

end
