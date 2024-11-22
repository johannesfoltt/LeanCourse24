import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Choose.Dvd
noncomputable section
open Function Ideal Polynomial Classical
open scoped Matrix
-- This is removed intentionally and should not be used manually in the exercises
attribute [-ext] LinearMap.prod_ext

/-! # Exercises to hand-in. -/

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff

set_option linter.unusedSectionVars false

variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R] [CharP R p] in
open Nat Finset in
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by {
  have hp' : p.Prime := hp.out
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p) := by {
  · ext n
    simp
    by_cases hn : n = 0
    · rw [hn]
      norm_num
      exact pos_of_neZero p
    · constructor
      · intro hnp
        right
        constructor
        · exact zero_lt_of_ne_zero hn
        · exact hnp
      intro hnp
      rcases hnp with hn₀ | hnp
      · exfalso
        exact hn hn₀
      · exact hnp.2
  }
  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by {
    intros i hi
    simp at hi
    refine Prime.dvd_choose hp' ?ha ?hab ?h
    · exact hi.2
    · refine Nat.sub_lt ?_ ?_
      · apply lt_trans
        · exact hi.1
        · exact hi.2
      · exact hi.1
    · rfl
  }
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by{
      apply Finset.sum_congr
      · rfl
      · intros i hi
        congr
        rw [CharP.cast_eq_zero_iff R p (p.choose i)]
        exact dvd_choose i hi
    }
    _ = 0 := by simp
  rw [add_pow, Finset.sum_range_succ, range_eq_insert_Ioo, Finset.sum_insert left_not_mem_Ioo, h6]
  simp
  ring
  }


section LinearMap

variable {R M₁ M₂ N M' : Type*} [CommRing R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup M']
  [Module R M₁] [Module R M₂] [Module R N] [Module R M']

/- Define the coproduct of two linear maps, and prove the characterization below.
Note that this proof works exactly the same for vector spaces over a field as it works
for modules over a ring, so feel free to think of `M₁`, `M₂`, `N` and `M'` as vector spaces.
You might recognize this as the characterization of a *coproduct* in category theory. -/

def coproduct (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun x := (f x.1) + (g x.2)
  map_add' x y := by {
    simp
    exact add_add_add_comm (f x.1) (f y.1) (g x.2) (g y.2)
  }
  map_smul' r x := by {
    simp
  }

-- this can be useful to have as a simp-lemma, and should be proven by `rfl`
@[simp] lemma coproduct_def (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  coproduct f g (x, y) = f x + g y := by {
    unfold coproduct
    simp
  }

lemma coproduct_unique {f : M₁ →ₗ[R] N} {g : M₂ →ₗ[R] N} {l : M₁ × M₂ →ₗ[R] N} :
    l = coproduct f g ↔
    l.comp (LinearMap.inl R M₁ M₂) = f ∧
    l.comp (LinearMap.inr R M₁ M₂) = g := by {
  constructor
  · intro hfg
    constructor
    · rw [hfg]
      ext x
      simp
    · rw [hfg]
      ext x
      simp
  · rintro ⟨hf, hg⟩
    ext x
    rw [← hf, ← hg]
    unfold coproduct
    simp
    rw [← LinearMap.map_add]
    simp
  }


end LinearMap
