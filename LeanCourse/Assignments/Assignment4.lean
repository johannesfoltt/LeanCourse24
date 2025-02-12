import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  sorry
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  sorry
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  sorry
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  sorry
  }

/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  sorry
  }


/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
  intros ε hε
  obtain ⟨N₀, hN₀⟩ := hs ε hε
  obtain ⟨N₁, hN₁⟩ := hr N₀
  use N₁
  intros n hn
  simp
  apply hN₀
  exact hN₁ n hn
  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
  intros ε hε
  obtain ⟨N₁, hN₁⟩ := hs₁ ε hε
  obtain ⟨N₃, hN₃⟩ := hs₃ ε hε
  use max N₁ N₃
  intros n hn
  rw [abs_lt]
  constructor
  · have h₂ := hs₁s₂ n
    have hnN₁ : n ≥ N₁ := by {
      exact le_of_max_le_left hn
    }
    calc -ε < s₁ n - a := by {
      have hN₁ := hN₁ n hnN₁
      exact (abs_lt.1 hN₁).1
    }
    _≤ s₂ n - a := by linarith
  · have h₃ := hs₂s₃ n
    have hnN₃ : n ≥ N₃ := by {
      exact le_of_max_le_right hn
    }
    calc s₂ n - a ≤ s₃ n - a := by linarith
    _< ε := by {
      have hN₃ := hN₃ n hnN₃
      exact (abs_lt.1 hN₃).2
    }
  }

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
  ext x
  simp
  constructor
  · rintro ⟨⟨x₁, hx₁⟩, hx⟩
    use x₁
    constructor
    · constructor
      · exact hx₁.1
      · rw [hx₁.2]
        exact hx
    · exact hx₁.2
  · rintro ⟨x₁, ⟨hx₁, hx⟩⟩
    constructor
    · use x₁
      constructor
      · exact hx₁.1
      · exact hx
    · rw [← hx]
      exact hx₁.2
  }

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext x
  simp
  have h₀ : (16:ℝ) = (4:ℝ) ^ 2 := by norm_num
  have h₁ : |(4:ℝ)| = 4 := by norm_num
  rw [h₀, sq_le_sq, h₁, le_abs, ← le_neg]
  tauto
  }


/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  unfold InjOn at hf
  unfold LeftInvOn
  use (fun y : β ↦ if h : ∃x₁, x₁ ∈ s ∧ f x₁  = y then Classical.choose h else default)
  intros x hx
  have h : ∃x₁, x₁ ∈ s ∧ f x₁ = f x := by use x
  simp [h]
  apply hf
  · exact (Classical.choose_spec h).1
  · exact hx
  · exact (Classical.choose_spec h).2
}


/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.
#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
-- h1' and h1'' might be useful later as arguments of `simp` to simplify your goal.
  have h1' : ∀ x y, f x ≠ g y := by {
    intros x y hxy
    rw [← propext (mem_empty_iff_false (f x)), ← h1]
    constructor
    · tauto
    · rw [hxy]
      tauto
    }
  have h1'' : ∀ y x, g y ≠ f x := by {
    intros y x hyx
    exact h1' x y (id (Eq.symm hyx))
  }
  have h2' : ∀ x, x ∈ range f ∪ range g := by {
    rw [h2]
    tauto
  }
  let L : Set α × Set β → Set γ :=
    (fun p : Set α × Set β ↦ f '' p.1 ∪ g '' p.2)
  let R : Set γ → Set α × Set β :=
    (fun s : Set γ ↦ (f ⁻¹' s , g ⁻¹' s))
  use L, R
  constructor
  · ext s x
    simp [R, L]
    constructor
    · intro h
      rcases h with ⟨x₁, hx₁⟩ | ⟨x₁,hx₁⟩
      repeat
      rw [← hx₁.2]
      exact hx₁.1
    · intro hx
      rcases h2' x with h | h
      · left
        obtain ⟨x₁, hx₁⟩ := h
        use x₁
        rw [hx₁]
        tauto
      · right
        obtain ⟨x₁, hx₁⟩ := h
        use x₁
        rw [hx₁]
        tauto
  · ext p x
    · simp [R, L]
      constructor
      · intro h
        rcases h with ⟨x₁, hx₁⟩ | ⟨x₁, hx₁⟩
        · rw [Injective.eq_iff hf] at hx₁
          rw [← hx₁.2]
          exact hx₁.1
        · exfalso
          exact h1'' x₁ x hx₁.2
      · intro hx
        left
        use x
    · simp [R, L]
      constructor
      · intro h
        rcases h with ⟨x₂, hx₂⟩ | ⟨x₂, hx₂⟩
        · exfalso
          exact h1' x₂ x hx₂.2
        · rw [Injective.eq_iff hg] at hx₂
          rw [← hx₂.2]
          exact hx₂.1
      · intro hx
        right
        use x
  }
