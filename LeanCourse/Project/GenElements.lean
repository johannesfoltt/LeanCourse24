import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open CategoryTheory ChosenFiniteProducts

/- recommended whenever you define anything new. -/
noncomputable section

abbrev gen_el {C : Type*} [Category C] [h : ChosenFiniteProducts C] (A : C) := ⊤_ C ⟶ A

abbrev appl {C : Type*} [Category C] [h : ChosenFiniteProducts C] {A B: C} (f : A ⟶ B) (x : gen_el A) := (x ≫ f : gen_el B)
