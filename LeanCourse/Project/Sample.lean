/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open CategoryTheory ChosenFiniteProducts Closed MonoidalCategory monoidalOfHasFiniteProducts

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/

variable (C : Type*) [Category C] [h : ChosenFiniteProducts C] [CartesianClosed C]
variable (A B X Y Z: C)
variable (φ: A ⟶ B ^^ A)
variable (g h: B ⟶ B)
variable (a : ⊤_ C ⟶ A)

abbrev point_surjective (Φ : A ⟶ B) :=
  ∀ (q : ⊤_ C ⟶ B), ∃ (p : ⊤_ C ⟶ A), (p ≫ Φ) = q

abbrev has_fixed_point (f : A ⟶ A) :=
  ∃ (s : ⊤_ C ⟶ A), (s ≫ f = s)

/-Construction of (q : (⊤ ⟶ (B ^^ A))):
q  := curry (q₀ : A × ⊤ ⟶ B)
q₀ := (Limits.prod.rightUnitor A).hom ≫ (q₁ : A ⟶ B)
q₁ := (A diag A × A) ≫ (q₂ : A × A ⟶ (B ^^ A) × A)
q₂ := (prod Φ id : A × A ⟶ (B ^^ A) × A) ≫ (q₃ : (B ^^ A) × A ⟶ B)
q₃ := (eval : (B ^^ A) × A ⟶ B) ≫ (f : B ⟶ B)
-/

#check CartesianClosed.curry ((Limits.prod.rightUnitor A).hom ≫ (Limits.diag A) ≫ (Limits.prod.map (𝟙 A) φ) ≫ ((exp.ev A).app B) ≫ g)
#check a ≫ (Limits.prod.rightUnitor A).inv ≫ (CartesianClosed.uncurry (a ≫ φ))

theorem Lawvere_fixed_point :
  (∃(Φ : A ⟶ B ^^ A), point_surjective C A (B ^^ A) Φ) → (∀(f : B ⟶ B), has_fixed_point C B f) := by {
    rintro ⟨Φ, hΦ⟩ f
    let q := CartesianClosed.curry ((Limits.prod.rightUnitor A).hom ≫ (Limits.diag A) ≫ (Limits.prod.map (𝟙 A) Φ) ≫ ((exp.ev A).app B) ≫ f)
    obtain ⟨p, hp⟩ := hΦ q
    use p ≫ (Limits.prod.rightUnitor A).inv ≫ (CartesianClosed.uncurry (p ≫ Φ))
    rw[eq_comm]
    calc p ≫ (Limits.prod.rightUnitor A).inv ≫ (CartesianClosed.uncurry (p ≫ Φ))
      = p ≫ (Limits.diag A) ≫ (Limits.prod.map (𝟙 A) Φ) ≫ ((exp.ev A).app B) ≫ f := by{
      rw [hp]
      unfold q
      simp
    }
    _= p ≫ (Limits.prod.rightUnitor A).inv ≫ (Limits.prod.map (𝟙 A) p) ≫ (Limits.prod.map (𝟙 A) Φ) ≫ ((exp.ev A).app B) ≫ f := by{
      sorry --diag_curry
    }
    _= p ≫ (Limits.prod.rightUnitor A).inv ≫ (Limits.prod.map (𝟙 A) (p ≫ Φ)) ≫ ((exp.ev A).app B) ≫ f := by{
      rw [Limits.prod.map_id_comp_assoc]
    }
    _= (p ≫ (Limits.prod.rightUnitor A).inv ≫ CartesianClosed.uncurry (p ≫ Φ)) ≫ f := by{
      rw [← CategoryTheory.CartesianClosed.homEquiv_symm_apply_eq]
      sorry
    }
  }

theorem Cantor_types (α : Type*) : ¬ ∃(f : α → Set α), Function.Surjective f := by {
 push_neg
 intro f
 unfold Function.Surjective
 push_neg
 sorry
}
