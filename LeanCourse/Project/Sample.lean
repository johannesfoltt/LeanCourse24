
/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open CategoryTheory ChosenFiniteProducts Closed MonoidalCategory monoidalOfHasFiniteProducts

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/

abbrev point_surj {C : Type*} [Category C] [ChosenFiniteProducts C] [CartesianClosed C] {A B : C} (Φ : A ⟶ B) :=
  ∀ (q : ⊤_ C ⟶ B), ∃ (p : ⊤_ C ⟶ A), (p ≫ Φ) = q

abbrev weakly_point_surj {C : Type*} [Category C] [ChosenFiniteProducts C] [CartesianClosed C] {X A B : C} (Φ : X ⟶ B ^^ A) :=
  ∀ (f : A ⟶ B), ∃ (x : ⊤_ C ⟶ X), ∀ (a : ⊤_ C ⟶ A), a ≫ f = (Limits.prod.lift a (x ≫ Φ)) ≫ (exp.ev A).app B

lemma point_surj_is_weakly_point_surj {C : Type*} [Category C] [ChosenFiniteProducts C] [CartesianClosed C] {X A B : C} :
  ∀(Φ : X ⟶ B ^^ A), point_surj Φ → weakly_point_surj Φ := by {
    intros Φ hΦ f
    unfold point_surj at hΦ
    obtain ⟨x, hx⟩ := hΦ (CartesianClosed.curry ((Limits.prod.rightUnitor A).1 ≫ f))
    use x
    intro a
    nth_rewrite 2 [← Category.comp_id a]
    rw [← Category.id_comp (x ≫ Φ), ← Limits.prod.lift_map, Category.assoc, ← CartesianClosed.uncurry_eq, hx]
    simp
  }

abbrev has_fixed_point {C : Type*} [Category C] [ChosenFiniteProducts C] [CartesianClosed C] {A : C} (f : A ⟶ A) :=
  ∃ (s : ⊤_ C ⟶ A), (s ≫ f = s)

theorem Lawvere_fixed_point {C : Type*} [Category C] [ChosenFiniteProducts C] [CartesianClosed C] {A B : C} :
  (∃(Φ : A ⟶ B ^^ A), weakly_point_surj Φ) → (∀(f : B ⟶ B), has_fixed_point f) := by {
    rintro ⟨Φ, hΦ⟩ f
    let q := (Limits.prod.lift (𝟙 A) Φ) ≫ ((exp.ev A).app B) ≫ f
    obtain ⟨p, hp⟩ := hΦ q
    use Limits.prod.lift p (p ≫ Φ) ≫ (exp.ev A).app B
    nth_rewrite 2 [← hp p]
    unfold q
    rw [Limits.prod.comp_lift_assoc]
    simp
  }

theorem Lawvere_fixed_point_types {α β : Type*} (F :  α → (α → β)) :
  Function.Surjective F → (∀(f : β → β), ∃ (s : β), f s = s) := by {
    intros hF f
    let q := (fun a ↦ f ((F a) a))
    obtain ⟨p, hp⟩ := hF q
    use (F p) p
    nth_rewrite 2 [hp]
    rfl
  }

theorem Lawvere_fixed_point_types_contrapositive {α β : Type*} (f : β → β) :
  (∀ s, f s ≠ s) → ∀(F :  α → (α → β)), ¬ Function.Surjective F := by {
    intros hf F hF
    obtain ⟨s, hs⟩ := Lawvere_fixed_point_types F hF f
    exact hf s hs
  }


lemma eq_iff_boolIndicator (α : Type*) (s t : Set α) :
  s = t ↔ (fun (a : α) ↦ Set.boolIndicator s a) = (fun (a : α) ↦ Set.boolIndicator t a) := by {
    constructor
    · intro hst
      rw [hst]
    · intro hst
      ext x
      constructor
      · rw [Set.mem_iff_boolIndicator, Set.mem_iff_boolIndicator]
        intro hx
        calc t.boolIndicator x = (fun a ↦ t.boolIndicator a) x := by simp
        _= (fun a ↦ s.boolIndicator a) x := by rw [hst]
        _= true := by assumption
      · rw [Set.mem_iff_boolIndicator, Set.mem_iff_boolIndicator]
        intro hx
        calc s.boolIndicator x = (fun a ↦ s.boolIndicator a) x := by simp
        _= (fun a ↦ t.boolIndicator a) x := by rw [hst]
        _= true := by assumption
  }


def Set_to_boolIndicator (α : Type*) : Set α → (α → Bool) := fun (s : Set α) ↦ (fun (a : α) ↦ Set.boolIndicator s a)

lemma Set_to_boolIndicator_Bijective {α : Type*} :
  Function.Bijective (Set_to_boolIndicator α) := by {
    unfold Set_to_boolIndicator
    constructor
    · intros s t
      simp
      exact (eq_iff_boolIndicator α s t).2
    · intro f
      simp
      use f ⁻¹' {true}
      ext x
      by_cases hx : f x = true
      · rw [hx, ← Set.mem_iff_boolIndicator]
        exact hx
      · rw [Bool.eq_false_eq_not_eq_true] at hx
        rw [hx, ← Set.not_mem_iff_boolIndicator]
        simp
        exact hx
  }

def boolNot : (Bool → Bool) := fun x ↦ ¬x

lemma boolNot_no_fixed_point : ∀(x : Bool), boolNot x ≠ x := by {
  intro x
  unfold boolNot
  by_cases hx : x = true
  · rw [hx]
    tauto
  · rw [Bool.eq_false_eq_not_eq_true] at hx
    rw [hx]
    tauto
}

theorem Cantor_types {α : Type*} : ∀(F : α → Set α), ¬ Function.Surjective F := by {
  intros F hF
  exact Lawvere_fixed_point_types_contrapositive boolNot boolNot_no_fixed_point ((Set_to_boolIndicator α) ∘ F) (Function.Surjective.comp Set_to_boolIndicator_Bijective.2 hF)
}
