import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function BigOperators Set Finset
open Classical

/-! # Exercises to hand-in. -/


/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type `X`. -/
def myEquivalenceRelation (X : Type*) : Setoid X where
  r x y := x = y
  iseqv := {
    refl := fun x ↦ rfl
    symm := by {intros x y h; rw [h]}
    trans := by {intros x y z hxy hyz; rw [hxy, hyz]}
  } -- Here you have to show that this is an equivalence.
                 -- If you click on the `sorry`, a lightbulb will appear to give the fields

/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (X : Type*) (x y : X) :
  letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl

/-
Now let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/

lemma id_lift (X : Type*) :
  letI := myEquivalenceRelation X; ∀ (a b : X), a ≈ b → id a = id b := by {
    intros a b h
    simp at h
    assumption
  }

def quotient_equiv_subtype (X : Type*) :
    Quotient (myEquivalenceRelation X) ≃ X where
      toFun := Quotient.lift id (id_lift X)
      invFun := Quotient.mk (myEquivalenceRelation X)
      left_inv := by {
        intro x
        induction x using Quotient.ind
        rename_i x
        apply Quotient.sound
        simp
      }
      right_inv := by {
        unfold Function.RightInverse
        intro x
        simp
      }



section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by {
  constructor
  · intro h
    rw [h]
    use 1
    simp
  · intro h
    ext a
    constructor
    · intro ha
      obtain ⟨g, hy⟩ := h
      obtain ⟨h, ha⟩ := ha
      simp at hy ha
      use (h * g⁻¹)
      simp
      calc (h * g⁻¹) • y = h • (g⁻¹ • y) := by {rw [mul_smul]}
      _= h • x := by {rw [← hy]; simp}
      _= a := by {exact ha}
    · intro ha
      obtain ⟨g, hy⟩ := h
      obtain ⟨h, ha⟩ := ha
      simp at hy ha
      use (h * g)
      simp
      rw [mul_smul, hy, ha]
  }

/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G where
  carrier := {g : G | g • x = x}
  mul_mem' := by {
    intros a b ha hb
    simp
    rw [mul_smul, hb, ha]
  }
  one_mem' := by simp
  inv_mem' := by {
    intros g hg
    simp
    simp at hg
    nth_rewrite 1 [← hg]
    simp
  }

-- This is a lemma that allows `simp` to simplify `x ≈ y` in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

/- Let's probe the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence.
(Note that we are coercing `orbitOf G x` to a (sub)type in the right-hand side) -/
--def orbit_map (x : X) := Set.codRestrict ...

lemma orbit_codomain (x : X) : ∀ (g : G), g • x ∈ orbitOf G x := by {intro g; use g}

def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x := by {
  letI := QuotientGroup.leftRel (stabilizerOf G x)
  have h :  (∀ (a b : G), a ≈ b → Set.codRestrict (fun g ↦ g • x) (orbitOf G x) (orbit_codomain G x) a = Set.codRestrict (fun g ↦ g • x) (orbitOf G x) (orbit_codomain G x) b) := by {
    intros a b hab
    rw [Subtype.ext_iff_val]
    simp
    simp at hab
    unfold stabilizerOf at hab
    simp at hab
    nth_rewrite 1 [← hab]
    rw [smul_smul]
    simp
  }
  let i : G ⧸ stabilizerOf G x → orbitOf G x := Quotient.lift (Set.codRestrict (fun g ↦ g • x) (orbitOf G x) (orbit_codomain G x)) h
  have hi : Bijective i := by {
    constructor
    · intros a b hab
      obtain ⟨a', ha⟩ := Quotient.exists_rep a
      obtain ⟨b', hb⟩ := Quotient.exists_rep b
      rw [← ha, ← hb]
      apply Quotient.sound
      simp
      unfold stabilizerOf
      rw [Subgroup.mem_mk]
      simp
      unfold i at hab
      rw [← ha, ← hb] at hab
      simp at hab
      rw [Subtype.ext_iff_val] at hab
      simp at hab
      rw[mul_smul, ← hab, ← mul_smul]
      simp
    · intros y
      obtain ⟨g, hg⟩ := y.2
      use ⟦g⟧
      exact SetCoe.ext hg
  }
  exact Equiv.ofBijective i hi
  }


end GroupActions
