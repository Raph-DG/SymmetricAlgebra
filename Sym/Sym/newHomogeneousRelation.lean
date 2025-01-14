import Mathlib
--import LieAlgCohomology.MissingLemmas.TwoSidedIdeal

/-
The interaction between TwoSidedIdeal and Ideals seems to be not as good as we'd expected, and another PR involving reconstructing two-sided ideals is currently being reviewed at #17908. So, we decided not to mess with TwoSidedIdeal. Instead, we will try to state and prove the necessary things in homogeneous relations. (which actually made things easier to use for SymmetricAlgebra)
-/

#check RingQuot.mkRingHom
#check RingQuot.mkAlgHom
#check Relation.EqvGen

variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {A : Type*} [Semiring A]

class IsHomogeneousRelation {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
(r : A → A → Prop) : Prop where
  is_homogeneous' : ∀ {x y : A}, r x y →
  ∀ i : ι, (Relation.EqvGen r) ((GradedRing.proj 𝒜 i) x) ((GradedRing.proj 𝒜 i) y)

namespace HomogeneousRelation

section RingCon

variable {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] (rel : A → A → Prop) [inst : IsHomogeneousRelation 𝒜 rel]

open Relation


lemma eqvGen_ringQuot_of_eqvGen {x y : A} (h : EqvGen rel x y) :
    EqvGen (RingQuot.Rel rel) x y :=
  Relation.EqvGen.mono (fun _ _ hab ↦ RingQuot.Rel.of hab) h



lemma add_left {x y : A} (h : rel x y) (i : ι) : 1 = 5 := sorry


instance : IsHomogeneousRelation 𝒜 (RingQuot.Rel rel) := ⟨by
  intro x y h n ; induction h
  case of x y h_rel =>
    apply eqvGen_ringQuot_of_eqvGen
    exact IsHomogeneousRelation.is_homogeneous' h_rel n
  case add_left a b c h_rel h =>
    rw [map_add, map_add]
    --refine RingQuot.Rel.add_left ?_ (a := ((GradedRing.proj 𝒜 n) a)) (b := ((GradedRing.proj 𝒜 n) b))
    apply eqvGen_ringQuot_of_eqvGen

    sorry



  case mul_left a b c h_rel h => sorry
  case mul_right a b c h_rel h => sorry

    ⟩

instance : IsHomogeneousRelation 𝒜 (Relation.EqvGen rel) := by
  apply IsHomogeneousRelation.mk
  rw [Equivalence.eqvGen_eq (Relation.EqvGen.is_equivalence rel)]
  sorry

instance : IsHomogeneousRelation 𝒜 (RingConGen.Rel rel) :=
  (RingQuot.eqvGen_rel_eq rel) ▸ inferInstance

end RingCon

section GradedRing

variable (𝒜 : ι → AddSubmonoid A) [GradedRing 𝒜] (rel : A → A → Prop) [IsHomogeneousRelation 𝒜 rel]

instance : GradedRing ((AddSubmonoid.map (RingQuot.mkRingHom rel)).comp 𝒜) := by
  sorry


end GradedRing

section GradedAlgebra

variable {R : Type*} [CommRing R] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (rel : A → A → Prop) [IsHomogeneousRelation 𝒜 rel]

instance : GradedAlgebra ((Submodule.map (RingQuot.mkAlgHom R rel)).comp 𝒜) := sorry

end GradedAlgebra

end HomogeneousRelation
