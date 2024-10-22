import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real

/-! # Exercises to hand-in. -/

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by {
  calc t ^ 2 - 3 * t - 17 ≥ t * (t - 3) - 17 := by linarith
  _ ≥ 10 * 7 - 17 := by {
    gcongr
    rw[← add_neg_cancel_right 7 3, sub_eq_add_neg]
    apply add_le_add_right
    norm_num
    assumption
  }
  _ = 53 := by norm_num
  _ ≥ 5 := by norm_num
  }

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by {
    calc t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = (t ^ 2 - 4 + 4) ^ 2 + 3 * (t ^ 2 - 4 + 4) * t - 3 * (t ^ 2 - 4 + 4) - 2 * t - 2 := by {
      ring
    }
    _ = 4 ^ 2 + 3 * 4 * t - 3 * 4 - 2 * t - 2 := by {
      rw[ht]
      ring
    }
    _ = 16 + 12 * t - 12 - 2 * t - 2 := by {
      norm_num
    }
    _ = 10 * t + 2 := by{
      ring
    }
  }

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by {
  calc n + 1 = n + m ^ 2 - m ^ 2 + 1 := by{
    ring
  }
  _ ≤ 2 - m ^ 2 + 1 := by{
    gcongr
    rw [add_comm]
    assumption
  }
  _ = 3 + - m ^ 2 := by{
    ring
  }
  _ ≤ 3 + 0 := by{
    norm_num
    exact pow_two_nonneg m
  }
  _ ≤ 3 + k ^ 2 := by{
    norm_num
    exact pow_two_nonneg k
  }
  }



section Min
variable (a b c : ℝ)

/- The following theorems characterize `min`.
Let's this characterization it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a := by {
  apply le_antisymm
  · apply le_min
    exact min_le_right a b
    exact min_le_left a b
  · apply le_min
    exact min_le_right b a
    exact min_le_left b a
  }

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by {
  apply le_antisymm
  · apply le_min
    · apply le_min
      apply min_le_left
      apply le_trans
      apply min_le_right
      apply min_le_left
    · apply le_trans
      apply min_le_right
      apply min_le_right
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    · apply le_min
      · apply le_trans
        apply min_le_left
        apply min_le_right
      · apply min_le_right
  }

end Min

/- Prove that the following function is continuous.
You can use `Continuous.div` as the first step,
and use the search techniques to find other relevant lemmas.
`ne_of_lt`/`ne_of_gt` will be useful to prove the inequality. -/
lemma exercise_continuity : Continuous (fun x ↦ (sin (x ^ 5) * cos x) / (x ^ 2 + 1)) := by {
  apply Continuous.div
  · apply Continuous.mul
    · apply Continuous.comp
      · exact Complex.continuous_re
      · sorry
    · exact continuous_cos
  · apply Continuous.add
    · exact continuous_pow 2
    · exact continuous_const
  sorry
  }

/- Prove this only using `intro`/`constructor`/`obtain`/`exact` -/
lemma exercise_and_comm : ∀ (p q : Prop), p ∧ q ↔ q ∧ p := by {
  intros p q
  constructor
  · intro h
    constructor
    · exact h.right
    · exact h.left
  · intro h
    constructor
    · exact h.right
    · exact h.left
  }


/-- Prove the following properties of nondecreasing functions. -/
def Nondecreasing (f : ℝ → ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

lemma exercise_nondecreasing_comp (f g : ℝ → ℝ) (hg : Nondecreasing g) (hf : Nondecreasing f) :
    Nondecreasing (g ∘ f) := by {
  intros x y h
  apply hg
  apply hf
  assumption
  }


/-- Note: `f + g` is the function defined by `(f + g)(x) := f(x) + g(x)`.
  `simp` can simplify `(f + g) x` to `f x + g x`. -/
lemma exercise_nondecreasing_add (f g : ℝ → ℝ) (hf : Nondecreasing f) (hg : Nondecreasing g) :
    Nondecreasing (f + g) := by {
    intros x y h
    simp
    calc f x + g x ≤ f y + g x := by {
      apply add_le_add_right
      exact hf x y h
    }
    _ ≤ f y + g y := by {
      apply add_le_add_left
      exact hg x y h
    }
  }



/-- Prove the following property of even. -/
def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

lemma exercise_even_iff (f g : ℝ → ℝ) (hf : EvenFunction f) :
    EvenFunction (f + g) ↔ EvenFunction g := by {
  constructor
  · intros hfg x
    calc g x = f x + g x - f x := by ring
    _ = (f + g) x - f x := by simp
    _ = (f + g) (-x) - f (-x):= by rw[hfg x, hf x]
    _ = f (-x) + g (-x) - f (-x) := by simp
    _ = g (-x) := by ring
  · intros hg x
    simp
    rw[hf x, hg x]

  }
