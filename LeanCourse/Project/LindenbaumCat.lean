import Mathlib

open CategoryTheory FirstOrder Language Limits

universe u u' v v' w

variable {L : Language} {α : Type u} [DecidableEq α]

def impForm (T : L.Theory) (φ : L.Formula α) := ∀ (M : Type w) [L.Structure M] [M ⊨ T], ∀ (v : α → M), φ.Realize v

def numVarTerm (t : L.Term α) := Finset.card (Term.varFinset t)

def numVarForm (φ : L.Formula α) := Finset.card (BoundedFormula.freeVarFinset φ)

structure LindenbaumCatofTheory (T : Theory L) where
  C : Type v
  isCat : Category.{w} C
  hasFiniteProducts : ChosenFiniteProducts C
  Ω : C
  A : C
  termToMap {α : Type u'} [DecidableEq α] (n : ℕ) (t : Term L α) (h : numVarTerm t = n) : (∏ᶜ fun _ : Fin n => A) ⟶ A
  formToMap {α : Type u'} [DecidableEq α] (n : ℕ) (φ : Formula L α) (h : numVarForm φ = n) : (∏ᶜ fun _ : Fin n => A) ⟶ Ω
  termMapEqIffEq {α : Type u'} [DecidableEq α] (n : ℕ) (t₁ t₂ : Term L (α ⊕ Fin 0)) (h₁ : numVarTerm t₁ = n) (h₂ : numVarTerm t₂ = n) : ((termToMap n t₁ h₁) = (termToMap n t₂ h₂)) ↔ (impForm T (BoundedFormula.equal t₁ t₂))
  formMapEqIffEqv {α : Type u'} [DecidableEq α] (n : ℕ) (φ₁ φ₂ : Formula L α) (h₁ : numVarForm φ₁ = n) (h₂ : numVarForm φ₂ = n) : (formToMap n φ₁ h₁ = formToMap n φ₂ h₂) ↔ (impForm T (φ₁.iff φ₂))
  constTermSubst {α : Type u'} [DecidableEq α] (n : ℕ) (φ : Formula L α) (hφ : numVarForm φ = n) (t : α → L.Term Empty) (ht : ∀ (i : α), numVarTerm (t i) = n) : formToMap n (BoundedFormula.subst φ t) ht =
