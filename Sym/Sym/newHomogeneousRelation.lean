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

open Relation GradedRing


lemma eqvGen_ringQuot_of_eqvGen {a b : A} (h : EqvGen rel a b) :
    EqvGen (RingQuot.Rel rel) a b :=
  Relation.EqvGen.mono (fun _ _ hab ↦ RingQuot.Rel.of hab) h

lemma eqvGen_add_right {a b c : A} (h : EqvGen (RingQuot.Rel rel) a b) :
    EqvGen (RingQuot.Rel rel) (a + c) (b + c) := by
  induction h with
  | rel x y hxy =>
    apply EqvGen.rel
    exact RingQuot.Rel.add_left hxy
  | refl x =>
    exact Quot.eqvGen_exact rfl
  | symm x y h1 h2 =>
    exact EqvGen.symm (x + c) (y + c) h2
  | trans x y z _ _ h1 h2 =>
    exact EqvGen.trans (x + c) (y + c) (z + c) h1 h2

lemma eqvGen_mul_left {a b c : A} (h : EqvGen (RingQuot.Rel rel) a b) :
    EqvGen (RingQuot.Rel rel) (a * c) (b * c) := by
  induction h with
  | rel x y hxy =>
    apply EqvGen.rel
    exact RingQuot.Rel.mul_left hxy
  | refl x =>
    exact Quot.eqvGen_exact rfl
  | symm x y h1 h2 =>
    exact EqvGen.symm (x * c) (y * c) h2
  | trans x y z _ _ h1 h2 =>
    exact EqvGen.trans (x * c) (y * c) (z * c) h1 h2

lemma eqvGen_add {a b c d: A} (hab : EqvGen (RingQuot.Rel rel) a b) (hcd : EqvGen (RingQuot.Rel rel) c d) :
    EqvGen (RingQuot.Rel rel) (a + c) (b + d) := by
  rw [RingQuot.eqvGen_rel_eq] at hab hcd ⊢
  exact RingConGen.Rel.add hab hcd


#check Finset.sum_induction
lemma Finset.relation_sum_induction {α : Type*} {s : Finset α} [DecidableEq α] {M : Type*} [AddCommMonoid M] (f : α → M) (g : α → M)
  (r : M → M → Prop) (hom : ∀ (a b c d : M), r a b → r c d → r (a + c) (b + d)) (unit : r 0 0) (base : ∀ x ∈ s, r (f x) (g x)) :
    r (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
  induction s using Finset.induction with
  | empty =>
    simpa only [Finset.sum_empty] using unit
  | insert _ _ =>
    simp_all only [Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp, not_false_eq_true,
      Finset.sum_insert]


lemma eqvGen_sum_mul {a b c : A} (n : ι) (h : ∀ (i : ι), EqvGen (RingQuot.Rel rel) ((proj 𝒜 i) a) ((proj 𝒜 i) b)) :
    EqvGen (RingQuot.Rel rel) ((proj 𝒜 n) (a * c)) ((proj 𝒜 n) (b * c)) := by
  haveI : (i : ι) → (x : ↥(𝒜 i)) → Decidable (x ≠ 0) :=
    fun i x ↦ Classical.propDecidable (x ≠ 0)
  repeat rw [proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
  let f : ι × ι → A :=
    fun ij ↦ ↑(((DirectSum.decompose 𝒜) a) ij.1) * ↑(((DirectSum.decompose 𝒜) c) ij.2)
  let g : ι × ι → A :=
    fun ij ↦ ↑(((DirectSum.decompose 𝒜) b) ij.1) * ↑(((DirectSum.decompose 𝒜) c) ij.2)
  have unit : EqvGen (RingQuot.Rel rel) 0 0 := by
    rw [RingQuot.eqvGen_rel_eq]
    exact RingConGen.Rel.refl 0
  -- have base : ∀ x ∈ Finset (ι × ι), r (f x) (g x) := sorry
  sorry






instance : IsHomogeneousRelation 𝒜 (RingQuot.Rel rel) := ⟨by
  intro x y h ; induction h
  case of x y h_rel =>
    intro n
    apply eqvGen_ringQuot_of_eqvGen
    exact IsHomogeneousRelation.is_homogeneous' h_rel n
  case add_left a b c h_rel h =>
    intro n
    rw [map_add, map_add]
    exact eqvGen_add_right rel (h n)
  case mul_left a b c h_rel h =>
    intro n
    haveI : (i : ι) → (x : ↥(𝒜 i)) → Decidable (x ≠ 0) :=
      fun i x ↦ Classical.propDecidable (x ≠ 0)
    simp [proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
    sorry

  case mul_right a b c h_rel h => sorry

    ⟩





instance : IsHomogeneousRelation 𝒜 (Relation.EqvGen rel) := by
  apply IsHomogeneousRelation.mk
  rw [Equivalence.eqvGen_eq (Relation.EqvGen.is_equivalence rel)]
  intro x y h
  induction h with
  | refl =>
    exact fun i ↦ Quot.eqvGen_exact rfl
  | symm x y _ h1 =>
    exact fun i ↦ EqvGen.symm ((GradedRing.proj 𝒜 i) x) ((GradedRing.proj 𝒜 i) y) (h1 i)
  | trans j k l _ _ h2 h3 =>
    exact fun i ↦
      EqvGen.trans ((GradedRing.proj 𝒜 i) j) ((GradedRing.proj 𝒜 i) k) ((GradedRing.proj 𝒜 i) l)
        (h2 i) (h3 i)
  | rel _ _ h4=>
    exact fun i ↦ IsHomogeneousRelation.is_homogeneous' h4 i

instance : IsHomogeneousRelation 𝒜 (RingConGen.Rel rel) :=
  (RingQuot.eqvGen_rel_eq rel) ▸ inferInstance

end RingCon

section GradedRing

variable (𝒜 : ι → AddSubmonoid A) [GradedRing 𝒜] (rel : A → A → Prop) [IsHomogeneousRelation 𝒜 rel]




instance : GradedRing ((AddSubmonoid.map (RingQuot.mkRingHom rel)).comp 𝒜) where
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
  decompose' := by
   sorry

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
