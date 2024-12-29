import LftCM.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · calc x <= 0 := by apply le_of_lt h
      _ <= |x| := by apply abs_nonneg




theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  calc (-x) <= |-x| := by apply le_abs_self (-x)
  _ <= |x| := by apply le_of_eq (abs_neg (x))

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    calc x + y <= x + |y| := by apply add_le_add_left (le_abs_self y)
    _ <= |x| + |y| := by apply add_le_add_right (le_abs_self x)
  · rw [abs_of_neg h]
    calc -(x + y) <= -x + -y := by linarith
    _ <= -x + |y| := by apply add_le_add_left (neg_le_abs_self y)
    _ <= |x| + |y| := by apply add_le_add_right (neg_le_abs_self x)


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · rcases le_or_gt 0 y with h' | h'
    · intro h
      rw [abs_of_nonneg h'] at h
      exact Or.inl h
    · intro h
      rw [abs_of_neg h'] at h
      exact Or.inr h
  · intro h
    rcases h with h | h
    · calc x < y := by apply h
      _ <= |y| := by apply le_abs_self
    · calc x < -y := by apply h
      _ <= |y| := by apply neg_le_abs_self




theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · rcases le_or_gt 0 x with h' | h'
    · intro h
      rw [abs_of_nonneg h'] at h
      obtain h1 :=
        calc 0 <= x := by apply h'
          _ < y := by apply h
      obtain k := neg_lt_neg_iff.mpr h1
      -- simp at k
      obtain h2 :=
        calc x >= 0 := by apply h'
          _ >= -0 := by linarith
          _ > -y := by apply k
      exact ⟨ h2, h ⟩
    · intro h
      obtain h2 :=
        calc x <= |x| := by apply le_abs_self
        _ < y := by apply h
      rw [abs_of_neg h'] at h
      obtain h1 := neg_lt_neg_iff.mpr h
      simp at h1
      exact ⟨h1, h2⟩
  · intro h
    rcases le_or_gt 0 x with h' | h'
    · rw [abs_of_nonneg h']
      exact h.right
    · rw [abs_of_neg h']
      apply neg_lt_neg_iff.mp
      simp
      exact h.left









end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  obtain ⟨x, y, h⟩ := h
  have k : x^2 + y^2 >= 0 := by
    calc x^2 + y^2 >= x^2 + 0 := by apply add_le_add_left (sq_nonneg y)
    _ >= 0 + 0 := by apply add_le_add_right (sq_nonneg x)
    _ >= 0 := by linarith

  rcases h with h | h
  · rw [h]
    apply k
  · rw [h]
    calc x^2 + y^2 + 1 >= 0 + 1 := by apply add_le_add_right (k)
    _ >= 0 := by linarith


example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [←sq_abs] at h
  have two_neq_zero :(2 : ℕ) ≠ 0 := by linarith

  have h₀ : |x| = 1 := by
    by_contra h₀
    if h': |x| < 1
    then
      have k : |x| ^2 < 1 := pow_lt_one (abs_nonneg x) h' two_neq_zero
      have k: |x| ^2  ≠ 1 := ne_of_lt k
      exact absurd h k
    else if h'': |x| = 1
    then exact absurd h'' h₀
    else
      have : ¬|x| <= 1 := by
        intro h
        have : |x| < 1 ∨ |x| = 1 := lt_or_eq_of_le h
        cases this with
        | inl h3 => exact h' h3
        | inr h3 => exact h'' h3
      have k: ¬|x| ^2  <= 1 := by apply mt (pow_le_one_iff_of_nonneg (abs_nonneg x) two_neq_zero).mp this
      have k: |x| ^2  > 1 := by linarith
      have k: |x| ^2  ≠ 1 := ne_of_gt k
      exact absurd h k
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at h₀
    apply Or.inl h₀
  · rw [abs_of_neg h] at h₀
    have :x = -1 := by linarith
    exact Or.inr this





example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  -- have : x^2 - y^2 = 0 := by linarith
  obtain this :=
    calc 0 = x^2 - y^2 := by linarith
      _ = (x - y) * (x + y) := by linarith
  -- rw [Eq.symm] at this
  have := Eq.symm this
  rw [mul_eq_zero] at this
  rcases this with h | h
  · have : x = y := by linarith
    exact Or.inl this
  · have : x = - y :=by linarith
    exact Or.inr this

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)


theorem aux (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
    -- have : x^2 - y^2 = 0 := by linarith
  obtain this :=
    calc  0 = y^2 - y^2 := by apply symm (sub_self (y^2))
      _ = x^2 - y ^2 := by rw [h]
      _ = (x - y) * (x + y) := by ring
  -- rw [Eq.symm] at this
  have := Eq.symm this
  rw [mul_eq_zero] at this
  rcases this with h | h
  · have : x = y := by
      apply add_neg_eq_zero.mp
      rw [←sub_eq_add_neg]
      apply h
    exact Or.inl this
  · have : x = - y := by
      apply add_neg_eq_zero.mp
      rw [neg_neg]
      apply h
    exact Or.inr this

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  obtain this :=
    calc x^2 = 1 := h
    _ = 1 ^ 2 := by ring
  apply aux
  apply this


end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  exact imp_iff_not_or
