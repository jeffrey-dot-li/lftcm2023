import LftCM.Common
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intros x y ε h1 h2 h3 h4
  rw [abs_mul]

  if h₀ : |x| * |y| = 0
  then
    rw [h₀]
    apply h1
  else
    have h₆: |x| ≠ 0 ∧ |y| ≠ 0 := by
      exact not_or.mp (mt mul_eq_zero.mpr h₀)
    have h₇ : |x| > 0 ∧ |y| > 0 := by
      constructor
      · exact (lt_iff_le_and_ne.mpr  ⟨(abs_nonneg x),  ( Ne.symm h₆.left)⟩)
      · exact (lt_iff_le_and_ne.mpr  ⟨(abs_nonneg y),  ( Ne.symm h₆.right)⟩)
    have h₈: |x| * |y| < |x| * ε := by
      rw [mul_lt_mul_left]
      exact h4
      exact h₇.left
    have h₉ : |x| < 1 := by
      apply lt_of_lt_of_le
      apply h3
      apply h2
    calc
      |x| * |y| < |x| * ε := by apply h₈
      |x| * ε < 1* ε := by
        rw [mul_lt_mul_right]
        apply h₉
        apply h1
      _ = ε := by ring









section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  apply my_lemma


section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  -- intro x y ε epos ele1 xlt ylt
  apply my_lemma

theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  -- intro x y ε epos ele1 xlt ylt
  apply my_lemma
  -- calc
  --   |x * y| = |x| * |y| := sorry
  --   _ ≤ |x| * ε := sorry
  --   _ < 1 * ε := sorry
  --   _ = ε := sorry

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  if h: (f x) = 0
  then
    rw[ h]
    rw [zero_mul]
  else
    rw [← mul_zero (f x)]
    rw [mul_le_mul_left]
    apply nng
    apply lt_iff_le_and_ne.mpr
    constructor
    · apply nnf
    · apply Ne.symm h




example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  dsimp
  have nnb: 0 <= b := by
    apply le_trans
    apply nng x
    apply hgb
  have nnab: 0 <= a * b := by
    apply mul_nonneg nna nnb
  if fzero: (f x) = 0
  then
    rw [fzero]
    rw [zero_mul]
    apply nnab
  else if fneg: (f x) < 0
    then
      have h:  (g x)  * (f x) <= 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos
        apply nng
        apply le_iff_lt_or_eq.mpr
        apply Or.inl fneg
      rw [mul_comm]
      apply le_trans
      apply h
      apply nnab
  else
    calc
      (f x) * (g x) <= a * (g x) := by
        apply mul_le_mul_of_nonneg_right
        apply hfa
        apply nng
      _ <= a * b := by
        apply mul_le_mul_of_nonneg_left
        apply hgb
        apply nna
end

section
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  dsimp
  have h : f a <= f b := by
    apply mf
    apply aleb
  apply mul_le_mul_of_nonneg_left
  apply h
  apply nnc



example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  dsimp
  have h: g a <= g b := by
    apply mg aleb
  apply mf
  apply h

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  apply Eq.symm
  calc (fun x ↦ f (x) * g (x)) (-x) =  f (-x) * g (-x) := rfl
    _ = - f (-x) * -g (-x) := by ring
    _ = f (x) * g (x)  := by rw [←of, ←og]



example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) (x) =  f (x) * g (x) := rfl
    _ = f (-x) * g (x) := by rw [ef]
    _ = f (-x) * -g (-x) := by rw [og]
    _ = - (f (-x) * g (-x)) := by ring
    _ = - (fun x ↦ f x * g x) (-x) := by rfl


example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  calc
  (fun x ↦ f (g x)) x = f (g x) := by rfl
  _ = f (-g x) := by rw [ef]
  _ = f ( - (-g (-x))) := by rw[og]
  _ = f ( g (-x)) := by ring



end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rss sst x xr
  have xs: x ∈ s := by apply rss xr
  apply sst xs

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intros x xs
  have xlea :x <= a := by apply h x xs
  have xleb : x <= b := by apply le_trans xlea h'
  exact xleb


end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x1 x2 h'
  have h2: c * x1 = c * x2 := by
    apply h'
  apply mul_left_cancel₀
  apply h
  apply h2





variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x1 x2 h1
  have h2 : g (f x1) = g (f x2) := by
    apply h1
  have h3: f x1 = f x2 := by
    rw[injg h2]

  rw [injf h3]



end
