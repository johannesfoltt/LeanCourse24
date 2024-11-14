import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  -- exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
  -- simp [myThree] -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)
  sorry


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  sorry
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  sorry
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  sorry
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  sorry
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  sorry
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  sorry
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  sorry
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  sorry
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  sorry
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  sorry
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  sorry
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  sorry
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  sorry
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  sorry
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  sorry
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  sorry
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- give definition here


/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

-- give definition here



/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := sorry



/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) := sorry



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