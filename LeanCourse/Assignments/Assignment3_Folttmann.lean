import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/-! # Exercises to hand-in. -/


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    rcases hx with hx₁ | hx₂
    · left
      use x
    · right
      use x
  · intro h
    rcases h with h₁ | h₂
    · obtain ⟨x, hx⟩ := h₁
      use x
      left
      exact hx
    · obtain ⟨x, hx⟩ := h₂
      use x
      right
      exact hx
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  constructor
  · intros h y
    obtain ⟨x, hx⟩ := h y
    use f x
    exact hx
  · intros h y
    obtain ⟨x₁, hx₁⟩ := h y
    obtain ⟨x₂, hx₂⟩ := hf x₁
    use x₂
    simp
    rw [hx₂, hx₁]
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  intro y
  obtain ⟨x, hx⟩ := hf ((y - 1) / 2)
  use (x/3 - 4)
  ring
  rw [hx]
  ring
  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  intro h
  unfold Surjective at h
  let R := {x | x ∉ f x}
  obtain ⟨r, hr⟩ := h R
  by_cases r ∈ R
  · apply hR
    rw [hr]
    exact hR
  · apply hR
    rw [← hr] at hR
    exact hR
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
  unfold SequentialLimit
  intros ε hε
  have hε₂ : ε/2 > 0 := by {
    apply div_pos
    · apply hε
    · norm_num
  }
  obtain ⟨N₁, hN₁⟩ := hs (ε/2) hε₂
  obtain ⟨N₂, hN₂⟩ := ht (ε/2) hε₂
  use max N₁ N₂
  intros n hn
  simp
  calc |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring
  _ ≤ |s n - a| + |t n - b| := by apply abs_add
  _ < |s n - a| + ε/2 := by {
    apply add_lt_add_of_le_of_lt
    · rfl
    · apply hN₂
      apply le_trans
      · apply le_max_right N₁ N₂
      . assumption
  }
  _ < ε/2 + ε/2 := by {
    apply add_lt_add_of_lt_of_le
    · apply hN₁
      apply le_trans
      · apply le_max_left N₁ N₂
      · assumption
    · rfl
  }
  _ = ε := by ring
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  unfold SequentialLimit
  intros ε hε
  rcases eq_or_ne c 0 with hc | hc
  · use 0
    intros n hn
    simp
    rw [hc]
    simp
    exact hε
  · have hcε : |c|⁻¹ * ε > 0 := by {
      apply mul_pos
      · apply inv_pos_of_pos
        simp
        exact hc
      · exact hε
    }
    obtain ⟨N, hN⟩ := hs (|c|⁻¹ * ε) hcε
    use N
    intros n hn
    simp
    calc |c * s n - c * a| = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ < |c| * |c|⁻¹ * ε := by{
      rw[mul_assoc]
      gcongr
      exact hN n hn
    }
    _ = ε := by {
      rw [Field.mul_inv_cancel]
      · ring
      · simp
        exact hc
    }
  }





section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {
  unfold EventuallyGrowsFaster
  intro k
  use k
  intros n hn
  simp
  gcongr
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
  unfold EventuallyGrowsFaster
  intro k
  obtain ⟨N₁, hN₁⟩ := h₁ k
  obtain ⟨N₂, hN₂⟩ := h₂ k
  use max N₁ N₂
  intros n hn
  simp
  ring
  gcongr
  · apply hN₁
    apply le_trans
    · apply le_max_left N₁ N₂
    · exact hn
  · apply hN₂
    apply le_trans
    · apply le_max_right N₁ N₂
    · exact hn
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  unfold EventuallyGrowsFaster
  simp
  use Nat.factorial
  constructor
  · intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · use 0
      intros n hn
      rw [hk]
      linarith
    · use k
      intros n hn
      have hn₁ : 0 < n + 1 := by {
        rw [← Nat.succ_eq_add_one, Nat.pos_iff_ne_zero]
        apply Nat.succ_ne_zero
      }
      rw [← Nat.mul_factorial_pred hn₁]
      simp
      gcongr
      linarith
  · intro n
    rw [← ne_eq, ← Nat.pos_iff_ne_zero]
    apply Nat.factorial_pos
  }

end Growth
