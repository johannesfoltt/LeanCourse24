import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace

/-! # Exercises to hand-in. -/

/- Here is a technical property using filters, characterizing when a 2-valued function converges to
a filter of the form `if q then F else G`. The next exercise is a more concrete application.
Useful lemmas here are
* `Filter.Eventually.filter_mono`
* `Filter.Eventually.mono` -/
lemma technical_filter_exercise {ι α : Type*} {p : ι → Prop} {q : Prop} {a b : α}
    {L : Filter ι} {F G : Filter α}
    (hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G) :
    (∀ᶠ i in L, p i ↔ q) ↔
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) := by {
  have hab : a ≠ b
  · exact haF hbF
  rw [tendsto_iff_eventually]
  constructor
  · intros hpq r hFG
    apply Filter.Eventually.mono hpq
    intros x hx
    rw [hx]
    by_cases hq : q
    · rw [if_pos hq]
      rw [if_pos hq] at hFG
      exact Filter.Eventually.filter_mono haF hFG
    · rw [if_neg hq]
      rw [if_neg hq] at hFG
      exact Filter.Eventually.filter_mono hbG hFG
  intro h
  by_cases hq : q
  · rw [if_pos hq] at h
    apply Filter.Eventually.mono (h hbF)
    intro x
    by_cases hp : p x
    · rw [if_pos hp]
      tauto
    · rw [if_neg hp]
      tauto
  · rw [if_neg hq] at h
    apply Filter.Eventually.mono (h haG)
    intro x
    by_cases hp : p x
    · rw [if_pos hp]
      tauto
    · rw [if_neg hp]
      tauto
  }

/- To be more concrete, we can use the previous lemma to prove the following.
if we denote the characteristic function of `A` by `1_A`, and `f : ℝ → ℝ` is a function,
then  `f * 1_{s i}` tends to `f * 1_t` iff `x ∈ s i` is eventually equivalent to
`x ∈ t` for all `x`. (note that this does *not* necessarily mean that `s i = t` eventually).
`f * 1_t` is written `indicator t f` in Lean.
Useful lemmas for this exercise are `indicator_apply`, `apply_ite` and `tendsto_pi_nhds`. -/
#check indicator_apply
#check apply_ite
lemma tendsto_indicator_iff {ι : Type*} {L : Filter ι} {s : ι → Set ℝ} {t : Set ℝ} {f : ℝ → ℝ}
    (ha : ∀ x, f x ≠ 0) :
    (∀ x, ∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔
    Tendsto (fun i ↦ indicator (s i) f) L (𝓝 (indicator t f)) := by {
  rw [tendsto_pi_nhds]
  have hi : ∀ (x : ℝ), (fun i ↦ (s i).indicator f x) = (fun i ↦ if x ∈ s i then f x else 0) := by {
    intro x
    ext i
    exact indicator_apply (s i) f x
  }
  have h0Nf : ∀ (x : ℝ), ∀ᶠ y in 𝓝 (f x), y ≠ 0 := by {
    intro x
    exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) (ha x)
  }
  have hfN0 : ∀ (x : ℝ), ∀ᶠ y in 𝓝 0, y ≠ f x := by {
    intro x
    exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) fun a ↦ ha x (id (Eq.symm a))
  }
  have hxNf : ∀ (x : ℝ), pure (f x) ≤ 𝓝 (f x) := by simp
  have h0N0 : pure (0 : ℝ) ≤ 𝓝 (0 : ℝ) := intervalIntegral.FTCFilter.pure_le
  constructor
  · intros h x
    rw [indicator_apply, hi, apply_ite 𝓝]
    exact (technical_filter_exercise (h0Nf x) (hfN0 x) (hxNf x) h0N0).1 (h x)
  · intros h x
    have hx := h x
    rw [indicator_apply, hi, apply_ite 𝓝] at hx
    exact (technical_filter_exercise (h0Nf x) (hfN0 x) (hxNf x) h0N0).2 (hx)
  }
