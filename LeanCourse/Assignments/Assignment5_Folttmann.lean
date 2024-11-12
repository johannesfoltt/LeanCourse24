import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical

/-This week I got stuck on a lot of simple proofs and then ran out of time.-/

/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here

@[ext] structure Strict_Bipointed_Type where
  α : Type*
  x₀ : α
  x₁ : α
  x₀_neq_x₁ : x₀ ≠ x₁

-- state and prove the lemma here

lemma neq_x₀_or_neq_x₁ (T : Strict_Bipointed_Type) : ∀z, z ≠ T.x₀ ∨ z ≠ T.x₁ := by{
  intro z
  by_cases h : z = T.x₀
  · right
    rw [h]
    exact T.x₀_neq_x₁
  · left
    assumption
}

/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    rw [sum_range_succ (fun i ↦ (i : ℚ) ^ 3), sum_range_succ (fun i ↦ (i : ℚ))]
    rw [ih, add_pow_two, add_assoc]
    congr
    sorry
  }

/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min -- this hypothesis allows you to use well-orderedness
  constructor
  · intros i j hij x
    simp
    intros hi hj
    ext y
    simp
    intros hy
    have hiy := hi hy
    have hjy := hj hy
    rw [hC] at hiy hjy
    simp at hiy hjy
    by_cases H₁ : i < j
    · tauto
    · by_cases H₂ : j < i
      · tauto
      · have H₃ := le_of_not_lt H₂
        have H₄ := le_of_not_lt H₁
        apply hij
        sorry
        --no matter how hard I try, I cannot use the Antisymmetry of the linear order
  · ext x
    simp
    constructor
    · rintro ⟨i, hi⟩
      use i
      rw [hC] at hi
      exact hi.1
    · rintro ⟨i, hi⟩
      let I := {j : ι| x ∈ A j}
      have hI : I.Nonempty := by tauto
      obtain ⟨j, hj⟩ := h I hI
      use j
      rw [hC]
      simp
      tauto
  }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  constructor
  · contrapose
    push_neg
    intro h
    obtain ⟨h₀, ⟨h₁, hab⟩⟩ := h
    rw [@prime_def_lt]
    constructor
    · sorry
    · rintro m hmn₁ ⟨k, hmk⟩
      by_contra
      have hk : 2 ≤ k := by {
        by_contra hk
        by_cases hk₀ : k = 0
        · rw [hk₀] at hmk
          apply h₀
          rw [hmk]
          rfl
        · sorry
      }
      have hm : 2 ≤ m := by sorry
      exact hab m k hm hk hmk
  · intros hn
    by_contra hp
    rcases hn with hn | hn | hn
    · exact Nat.Prime.ne_zero hp hn
    · exact Nat.Prime.ne_one hp hn
    · rw [@prime_def_lt''] at hp
      rcases hn with ⟨a, ⟨b, hab⟩⟩
      have han : a ∣ n := by {use b; exact hab.2.2}
      rcases hp.2 a han with ha | ha
      · rw [ha] at hab
        tauto
      · rw [ha] at hab
        have hn : n ≠ 0 := by linarith
        have hb : b = 1 := by {
          rw [← propext (mul_eq_left hn)]
          tauto
        }
        rw [hb] at hab
        tauto
  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · norm_num at hn
  · norm_num at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
  have h2 : 2 ^ 2 ≤ 2 ^ a := by sorry
  have h3 : 1 ≤ 2 ^ a := by sorry
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    sorry
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by sorry
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  sorry
  }

/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
  by_contra h
  push_neg at h
  obtain ⟨ha₂, hb₂⟩ := h
  obtain ⟨n, hn⟩ := ha₂
  obtain ⟨m, hm⟩ := hb₂
  have hnab : (b : ℤ) = ((n : ℤ) + (a : ℤ)) * ((n : ℤ) - (a : ℤ)) := by linarith
  have hmab : (a : ℤ) = ((m : ℤ) + (b : ℤ)) * ((m : ℤ) - (b : ℤ)) := by linarith
  have hna₀ : 0 < (n : ℤ) - (a : ℤ) := by {simp; rw [← mul_self_lt_mul_self_iff]; linarith}
  have hna₁ : 0 < (n : ℤ) + (a : ℤ) := by linarith
  have hab : (a : ℤ) < (b : ℤ) := by {
    calc (a : ℤ) < 2 * (a : ℤ) := by linarith
    _= (n + a) - (n - a) := by ring
    _≤ n + a := by linarith
    _= (n + a) * 1 := by ring
    _≤ b := by {rw [hnab]; gcongr; linarith}
  }
  have hmb₀ : 0 < (m : ℤ) - (b : ℤ) := by {simp; rw [← mul_self_lt_mul_self_iff]; linarith}
  have hnb₁ : 0 < (m : ℤ) + (a : ℤ) := by linarith
  have hba : (b : ℤ) < (a : ℤ) := by {
    calc (b : ℤ) < 2 * (b : ℤ) := by linarith
    _= (m + b) - (m - b) := by ring
    _≤ m + b := by linarith
    _= (m + b) * 1 := by ring
    _≤ a := by {rw [hmab]; gcongr; linarith}
  }
  exact Int.lt_irrefl (a : ℤ) (Int.lt_trans hab hba)
  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

def groupPosReal : Group PosReal where
  mul := (fun a b ↦ a * b)
  mul_assoc := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  inv := Subtype.map (fun (x : ℝ) ↦ x⁻¹) (by {intros a ha; exact inv_pos_of_pos ha})
  inv_mul_cancel := by {
    intro a
    apply Subtype.ext_val
    simp
    ring
    sorry
  }

variable (a b : PosReal)

/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] card_powerset
#check Finset.induction

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by {
  induction s using Finset.induction with
  | empty =>
    rfl
  | @insert x s hxs ih =>
    sorry
  }
