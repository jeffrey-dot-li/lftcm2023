import LftCM.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · exact h₀
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  constructor
  apply h.left
  intro h'
  have ⟨h₀, h₁⟩ := h
  dsimp only [Dvd.dvd] at h'
  obtain ⟨c, cmul⟩ := h'
  dsimp only [Dvd.dvd] at h
  obtain ⟨d, dmul ⟩ := h.left
  rw [dmul] at cmul
  have : m * 1 = m * (d * c) := by linarith
  have m_not_zero: m ≠ 0 := by
    intro meq0
    rw [meq0] at dmul
    contrapose! h₁
    linarith

  have this: 1 = d * c := mul_left_cancel₀ m_not_zero this
  have : (d=1)∧ (c=1):= by
    apply mul_eq_one.mp
    rw [this]

  rw [this.left] at dmul
  rw [mul_one] at dmul
  have meqn : m = n := by exact Eq.symm dmul
  have : ¬m = n := by
    apply h.right
  exact absurd meqn this







example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  rw [not_le]
  calc
    x ≤ y ∧  x < y  ↔  x < y := by
      constructor
      · intro h
        exact h.right
      · intro h
        exact ⟨le_of_lt h, h⟩

    _ ↔ x ≤ y ∧ x ≠ y := by
      constructor
      · intro h
        exact ⟨le_of_lt h, ne_of_lt h⟩
      · intro h
        contrapose! h
        intro h'
        apply Eq.symm (le_antisymm h h')





theorem aux2 {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x ^ 2 = 0 := by
  have : y ^ 2 >= 0 := by apply sq_nonneg
  have xgeq0 : x^2 >= 0 := by apply sq_nonneg
  have xleq0 :=
    calc x^2 =(x^2 + y^2) - y^2 := by linarith
      _ <= 0 - 0 := by
        apply sub_le_sub
        apply le_of_eq
        apply h
        linarith
      _ = 0 := by linarith
  apply le_antisymm xleq0 xgeq0





example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h0 : x^2 = 0 := by apply aux2 h
    rw [add_comm] at h
    have h1 : y^2 = 0 := by apply aux2 h
    obtain x_zero := pow_eq_zero h0
    obtain y_zero := pow_eq_zero h1
    exact ⟨x_zero,  y_zero⟩
  · intro ⟨x_zero,  y_zero⟩
    rw [x_zero,  y_zero]
    linarith

section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  intro h
  dsimp only [Monotone] at h
  have : (0: ℝ ) <= (1 : ℝ) := by linarith
  obtain h' := h this
  linarith

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  calc
    a < b ↔ a ≤ b ∧ a ≠ b := by
      constructor
      · intro h
        exact ⟨le_of_lt h, ne_of_lt h⟩
      · intro ⟨h0, h1⟩
        apply lt_of_le_of_ne h0 h1
end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_le]
  intro ⟨h0, h1⟩
  exact absurd h0 h1

example : a < b → b < c → a < c := by
  apply lt_trans


end
