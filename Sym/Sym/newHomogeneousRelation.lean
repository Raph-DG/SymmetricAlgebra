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

instance : IsHomogeneousRelation 𝒜 (RingQuot.Rel rel) := by
  apply IsHomogeneousRelation.mk
  intro x y h n
  induction h with
  | of h => sorry
  | add_left _ _ => sorry
  | mul_left _ _ => sorry
  | mul_right _ _ => sorry





instance : IsHomogeneousRelation 𝒜 (Relation.EqvGen rel) := by
  apply IsHomogeneousRelation.mk
  rw [Equivalence.eqvGen_eq (Relation.EqvGen.is_equivalence rel)]
  intro x y h
  induction h with
  | refl =>
    exact fun i ↦ Quot.eqvGen_exact rfl
  | symm x h_ih y j =>
    exact fun i ↦ EqvGen.symm ((GradedRing.proj 𝒜 i) x) ((GradedRing.proj 𝒜 i) h_ih) (j i)
  | trans j k h_ih₁ h_ih₂ h1 h2 h3 =>
    exact fun i ↦
      EqvGen.trans ((GradedRing.proj 𝒜 i) j) ((GradedRing.proj 𝒜 i) k) ((GradedRing.proj 𝒜 i) h_ih₁)
        (h2 i) (h3 i)
  | rel r s t=>
    exact fun i ↦ IsHomogeneousRelation.is_homogeneous' t i

instance : IsHomogeneousRelation 𝒜 (RingConGen.Rel rel) :=
  (RingQuot.eqvGen_rel_eq rel) ▸ inferInstance

end RingCon

section GradedRing

variable (𝒜 : ι → AddSubmonoid A) [GradedRing 𝒜] (rel : A → A → Prop) [IsHomogeneousRelation 𝒜 rel]
#check RingQuot.mkRingHom rel

instance : GradedRing ((AddSubmonoid.map (RingQuot.mkRingHom rel)).comp 𝒜) where
  --'one_mem', 'mul_mem', 'decompose'', 'left_inv', 'right_inv'
  one_mem := by
    use 1
    constructor
    · exact SetLike.GradedOne.one_mem
    · exact map_one (RingQuot.mkRingHom rel)
  mul_mem := by
    intro x y gi gj hi hj
    simp only [Function.comp_apply, Submodule.mem_map]
    simp only [Function.comp_apply, Submodule.mem_map] at hj
    simp only [Function.comp_apply, Submodule.mem_map] at hi
    rcases hi with ⟨a, ha1, ha2⟩
    rcases hj with ⟨b, hb1, hb2⟩
    use a * b
    constructor
    · exact SetLike.GradedMul.mul_mem ha1 hb1
    · simp only [map_mul]
      exact Mathlib.Tactic.LinearCombination'.mul_pf ha2 hb2
  decompose' := sorry

  left_inv := sorry

  right_inv := sorry





end GradedRing

section GradedAlgebra

variable {R : Type*} [CommRing R] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (rel : A → A → Prop) [IsHomogeneousRelation 𝒜 rel]

instance : GradedAlgebra ((Submodule.map (RingQuot.mkAlgHom R rel)).comp 𝒜) where
  one_mem := by
    use 1
    constructor
    · exact SetLike.GradedOne.one_mem
    · exact map_one (RingQuot.mkAlgHom R rel)
  mul_mem := by
    intro x y gi gj hi hj
    simp only [Function.comp_apply, Submodule.mem_map]
    simp only [Function.comp_apply, Submodule.mem_map] at hj
    simp only [Function.comp_apply, Submodule.mem_map] at hi
    rcases hi with ⟨a, ha1, ha2⟩
    rcases hj with ⟨b, hb1, hb2⟩
    use a * b
    constructor
    · exact SetLike.GradedMul.mul_mem ha1 hb1
    · simp only [map_mul]
      exact Mathlib.Tactic.LinearCombination'.mul_pf ha2 hb2
  decompose' := sorry

  left_inv := sorry

  right_inv := sorry

end GradedAlgebra

end HomogeneousRelation
