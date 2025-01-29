import Mathlib

open CategoryTheory Limits Closed

universe u v

variable {C : Type*} [Category C]
variable {W X Y Z : C}

structure HasPullbackTop (left : W ⟶ Y) (bottom : Y ⟶ Z) (right : X ⟶ Z) where
    top : W ⟶ X
    comm : top ≫ right = left ≫ bottom
    is_pb : IsLimit (PullbackCone.mk _ _ comm)

abbrev classifying {Ω Ω₀ U X : C} (truth : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) := HasPullbackTop f χ truth

structure IsSubobjectClassifier {Ω Ω₀ : C} (truth : Ω₀ ⟶ Ω) where
    classifier_of : ∀ {U X} (f : U ⟶ X) [Mono f], X ⟶ Ω
    classifies' : ∀ {U X} (f : U ⟶ X) [Mono f], classifying truth f (classifier_of f)
    uniquely' : ∀ {U X} (f : U ⟶ X) [Mono f] (χ₁ : X ⟶ Ω), classifying truth f χ₁ → classifier_of f = χ₁

variable (C)

class HasSubobjectClassifier where
    Ω : C
    Ω₀ : C
    truth : Ω₀ ⟶ Ω
    truth_mono : Mono truth
    is_subobj_classifier : IsSubobjectClassifier truth

variable (C : Type*) [Category C] [HasSubobjectClassifier C]

def Ω : C := HasSubobjectClassifier.Ω
def Ω₀ : C := HasSubobjectClassifier.Ω₀
def truth : Ω₀ C ⟶ Ω C := HasSubobjectClassifier.truth
instance truthMono : Mono (truth C) := HasSubobjectClassifier.truth_mono
def SubobjClassifierIsSubobjClassifier : IsSubobjectClassifier (truth C) := HasSubobjectClassifier.is_subobj_classifier

variable {C}

def ClassifierOf {U X : C} (f : U ⟶ X) [Mono f] : X ⟶ Ω C :=
(SubobjClassifierIsSubobjClassifier C).classifier_of f
def Classifies {U X : C} (f : U ⟶ X) [Mono f] : classifying (truth C) f (ClassifierOf f) :=
(SubobjClassifierIsSubobjClassifier C).classifies' f
lemma Uniquely {U X : C} (f : U ⟶ X) [Mono f] (χ₁ : X ⟶ Ω C) (hχ : classifying (truth C) f χ₁) : ClassifierOf f = χ₁ :=
(SubobjClassifierIsSubobjClassifier C).uniquely' f χ₁ hχ

variable (C : Type*) [Category C]

class Topos where
    lim : HasFiniteLimits C
    sub : HasSubobjectClassifier C
    cc : CartesianClosed C

variable {D : Type*} [Category D] [Topos D]
