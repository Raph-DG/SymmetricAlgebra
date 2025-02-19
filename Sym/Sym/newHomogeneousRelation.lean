/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiming Fu, Zhenyan Fu, ZhiXuan Dai, Raphael Douglas Giles, Jiedong Jiang, Jingting Wang
-/
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous Relation

-/
#check RingQuot.mkRingHom
#check RingQuot.mkAlgHom
#check Relation.EqvGen

variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {A : Type*} [Semiring A]

class IsHomogeneousRelation {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
  [GradedRing 𝒜] (r : A → A → Prop) : Prop where
  is_homogeneous' : ∀ {x y : A}, r x y →
  ∀ i : ι, (Relation.EqvGen r) ((GradedRing.proj 𝒜 i) x) ((GradedRing.proj 𝒜 i) y)

namespace HomogeneousRelation

section RingCon

variable {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] (rel : A → A → Prop)

open Relation GradedRing

lemma eqvGen_ringQuot_of_eqvGen {a b : A} (h : EqvGen rel a b) :
    EqvGen (RingQuot.Rel rel) a b := Relation.EqvGen.mono (fun _ _ h' ↦ RingQuot.Rel.of h') h

lemma eqvGen_ringQuot_add_right {a b c : A} (h : EqvGen (RingQuot.Rel rel) a b) :
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

lemma eqvGen_ringQuot_mul_left {a b c : A} (h : EqvGen (RingQuot.Rel rel) a b) :
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

lemma eqvGen_ringQuot_mul_right {a b c : A} (h : EqvGen (RingQuot.Rel rel) a b) :
    EqvGen (RingQuot.Rel rel) (c * a) (c * b) := by
  induction h with
  | rel x y hxy =>
  apply EqvGen.rel
  exact RingQuot.Rel.mul_right hxy
  | refl x =>
  exact Quot.eqvGen_exact rfl
  | symm x y h1 h2 =>
  exact EqvGen.symm (c * x) (c * y) h2
  | trans x y z _ _ h1 h2 =>
  exact EqvGen.trans (c * x) (c * y) (c * z) h1 h2

lemma Finset.relation_sum_induction {α : Type*} {s : Finset α} [DecidableEq α]
    {M : Type*} [AddCommMonoid M] (f : α → M) (g : α → M) (r : M → M → Prop)
    (hom : ∀ (a b c d : M), r a b → r c d → r (a + c) (b + d)) (unit : r 0 0)
    (base : ∀ x ∈ s, r (f x) (g x)) :
    r (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
  induction s using Finset.induction with
  | empty => simpa
  | insert _ _ => simp_all

lemma coe_mul_sum_support_subset {ι : Type*} {σ : Type*} {R : Type*} [DecidableEq ι] [Semiring R]
    [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ) [AddMonoid ι] [SetLike.GradedMonoid A]
    [(i : ι) → (x : ↥(A i)) → Decidable (x ≠ 0)] (r r' : DirectSum ι fun i ↦ ↥(A i))
    {S T: Finset ι} (hS : DFinsupp.support r ⊆ S) (hT : DFinsupp.support r' ⊆ T)
    (p : ι × ι → Prop) [DecidablePred p] :
    ∑ ij ∈ Finset.filter p (DFinsupp.support r ×ˢ DFinsupp.support r'), ((r ij.1) * (r' ij.2) : R) =
    ∑ ij ∈ Finset.filter p (S ×ˢ T), ((r ij.1) * (r' ij.2) : R) := by
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_subset (Finset.product_subset_product hS hT)
  intro x _ hx
  simp only [Finset.mem_product, DFinsupp.mem_support_toFun, ne_eq, not_and, not_not] at hx
  have : ((r x.1) * (r' x.2) : R) = 0 := by
    by_cases h : r x.1 = 0
    · simp [h]
    · simp [hx h]
  simp [this]

noncomputable local instance : (i : ι) → (x : ↥(𝒜 i)) → Decidable (x ≠ 0) :=
    fun _ x ↦ Classical.propDecidable (x ≠ 0)

theorem eqvGen_proj_mul_right {a b c : A} (n : ι)
    (h : ∀ (i : ι), EqvGen (RingQuot.Rel rel) ((proj 𝒜 i) a) ((proj 𝒜 i) b)) :
    EqvGen (RingQuot.Rel rel) ((proj 𝒜 n) (a * c)) ((proj 𝒜 n) (b * c)) := by
  simp only [proj_apply] at h
  simp only [proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
  rw [coe_mul_sum_support_subset 𝒜 _ _ Finset.subset_union_left (Set.Subset.refl _),
    coe_mul_sum_support_subset 𝒜 _ _ Finset.subset_union_right (Set.Subset.refl _)]
  apply Finset.relation_sum_induction _ _ (EqvGen (RingQuot.Rel rel))
  · intro _ _ _ _ hab hcd
    rw [RingQuot.eqvGen_rel_eq] at hab hcd ⊢
    exact RingConGen.Rel.add hab hcd
  · rw [RingQuot.eqvGen_rel_eq]
    exact RingConGen.Rel.refl 0
  · exact fun x _ => eqvGen_ringQuot_mul_left rel (h x.1)

theorem eqvGen_proj_mul_left {a b c : A} (n : ι)
    (h : ∀ (i : ι), EqvGen (RingQuot.Rel rel) ((proj 𝒜 i) a) ((proj 𝒜 i) b)) :
    EqvGen (RingQuot.Rel rel) ((proj 𝒜 n) (c * a)) ((proj 𝒜 n) (c * b)) := by
  simp only [proj_apply] at h
  simp only [proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
  rw [coe_mul_sum_support_subset 𝒜 _ _ (Set.Subset.refl _) Finset.subset_union_left,
    coe_mul_sum_support_subset 𝒜 _ _ (Set.Subset.refl _) Finset.subset_union_right]
  apply Finset.relation_sum_induction _ _ (EqvGen (RingQuot.Rel rel))
  · intro _ _ _ _ hab hcd
    rw [RingQuot.eqvGen_rel_eq] at hab hcd ⊢
    exact RingConGen.Rel.add hab hcd
  · rw [RingQuot.eqvGen_rel_eq]
    exact RingConGen.Rel.refl 0
  · exact fun x _ => eqvGen_ringQuot_mul_right rel (h x.2)

variable [IsHomogeneousRelation 𝒜 rel]

instance : IsHomogeneousRelation 𝒜 (RingQuot.Rel rel) := ⟨by
  intro x y h ; induction h
  case of x y h_rel =>
    intro n
    apply eqvGen_ringQuot_of_eqvGen
    exact IsHomogeneousRelation.is_homogeneous' h_rel n
  case add_left a b c h_rel h =>
    intro n
    rw [map_add, map_add]
    exact eqvGen_ringQuot_add_right rel (h n)
  case mul_left a b c h_rel h =>
    intro n
    exact eqvGen_proj_mul_right 𝒜 rel n h
  case mul_right c a b h_rel h =>
    intro n
    exact eqvGen_proj_mul_left 𝒜 rel n h⟩

instance : IsHomogeneousRelation 𝒜 (Relation.EqvGen rel) := ⟨by
  rw [Equivalence.eqvGen_eq (Relation.EqvGen.is_equivalence rel)]
  intro x y h
  induction h with
  | refl => exact fun i ↦ Quot.eqvGen_exact rfl
  | symm x y _ h1 =>
    exact fun i ↦ EqvGen.symm ((GradedRing.proj 𝒜 i) x) ((GradedRing.proj 𝒜 i) y) (h1 i)
  | trans j k l _ _ h2 h3 =>
    exact fun i ↦
      EqvGen.trans ((GradedRing.proj 𝒜 i) j) ((GradedRing.proj 𝒜 i) k) ((GradedRing.proj 𝒜 i) l)
      (h2 i) (h3 i)
  | rel _ _ h4 =>
    exact fun i ↦ IsHomogeneousRelation.is_homogeneous' h4 i⟩

instance : IsHomogeneousRelation 𝒜 (RingConGen.Rel rel) :=
  (RingQuot.eqvGen_rel_eq rel) ▸ inferInstance

end RingCon

noncomputable section GradedRing

open DirectSum

variable (𝒜 : ι → AddSubmonoid A) [inst : GradedRing 𝒜] (rel : A → A → Prop)

local instance : (i : ι) → (x : ↥(𝒜 i)) → Decidable (x ≠ 0) :=
  fun _ x ↦ Classical.propDecidable (x ≠ 0)

instance : (i : ι) →  DecidableEq ↥((AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i) :=
  fun i ↦ Classical.typeDecidableEq ↥((AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i)


abbrev choose (rel : A → A → Prop) (a : RingQuot rel) :=
  Classical.choose <| (RingQuot.mkRingHom_surjective rel) a

abbrev choose_spec (rel : A → A → Prop) (a : RingQuot rel) : (RingQuot.mkRingHom rel) (choose rel a) = a :=
  Classical.choose_spec <| (RingQuot.mkRingHom_surjective rel) a

instance : SetLike.GradedMonoid ((AddSubmonoid.map (RingQuot.mkRingHom rel)).comp 𝒜) where
  one_mem := ⟨1, ⟨SetLike.GradedOne.one_mem, map_one (RingQuot.mkRingHom rel)⟩⟩
  mul_mem := by
    intro x y gi gj hi hj
    simp only [Function.comp_apply, Submodule.mem_map]
    rcases hi with ⟨a, ha1, ha2⟩
    rcases hj with ⟨b, hb1, hb2⟩
    use a * b
    constructor
    · exact SetLike.GradedMul.mul_mem ha1 hb1
    · rw [map_mul, ha2, hb2]


variable [IsHomogeneousRelation 𝒜 rel]


-- def decompose2 (a : RingQuot rel) : DirectSum ι fun i ↦ (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i :=
--   DirectSum.mk (fun i ↦ (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i)
--     (inst.decompose' <| choose rel a).support fun i ↦  decomposeAux 𝒜 rel a i


lemma map_ZerotoZero (i : ι) : ((DirectSum.decompose 𝒜) (choose rel 0)) i = 0 := by
   sorry


def decomposeAux (a : RingQuot rel) (i : ι) : (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i :=
  ⟨⟨Quot.lift (fun a ↦ Quot.mk _ (inst.decompose' a i))
    (fun a b h ↦ Quot.eq.mpr <| IsHomogeneousRelation.is_homogeneous' h i) a.toQuot⟩, by
    obtain ⟨⟨a⟩⟩ := a; exact ⟨inst.decompose' a i, by simp, by simp [RingQuot.mkRingHom]⟩⟩


/-- The `decompose'` argument of `RingQuotGradedRing`. -/
def decompose' : RingQuot rel →+ DirectSum ι fun i ↦ (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i where
  toFun a := DirectSum.mk (fun i ↦ (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i)
      (inst.decompose' <| choose rel a).support fun i ↦ decomposeAux 𝒜 rel a i
  map_zero' := by
    simp only [Function.comp_apply, DirectSum.Decomposition.decompose'_eq, Finset.coe_sort_coe]
    unfold DirectSum.mk
    simp only [Finset.coe_sort_coe, AddMonoidHom.coe_mk, ZeroHom.coe_mk, DFinsupp.mk_apply,
      DFinsupp.mem_support_toFun, ne_eq, Classical.dite_not]
    apply DFinsupp.ext
    intro i
    rw [DFinsupp.mk_apply]
    simp only [DFinsupp.mem_support_toFun, ne_eq, dite_eq_ite, Classical.ite_not]
    rw [if_pos]
    · rfl
    · exact map_ZerotoZero 𝒜 rel i

    -- -- The zero element in the direct sum is the function that returns zero for all indices.
    -- -- Since `decompose'` is defined in terms of `inst.decompose'`, and `inst.decompose'` is a graded ring decomposition,
    -- -- it should map zero to zero.

  map_add' := by
    intro x y
    unfold DirectSum.mk
    apply DFinsupp.ext
    intro i
    simp only [Function.comp_apply, DirectSum.Decomposition.decompose'_eq, Finset.coe_sort_coe,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, DFinsupp.mk_apply, DFinsupp.mem_support_toFun, ne_eq,
      dite_eq_ite, Classical.ite_not, DirectSum.add_apply]
    --rw [if_pos]
    sorry




set_option maxHeartbeats 0

--lemma decompose''_eq_decompose' : decompose'' 𝒜 rel = decompose' 𝒜 rel := rfl



lemma decompose'_of_eq (a : RingQuot rel) (i : ι)
    (ha : a ∈ (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i) :
    (((decompose' 𝒜 rel) a) i) = a := by
  sorry



    --lift a to (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i using ha



lemma decompose'_of_ne'  (i j : ι) (ne : i ≠ j)
    (a : ((AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i)) :
    ((decompose' 𝒜 rel a) j) = 0 := by
  sorry


lemma decompose'_of_ne (a : RingQuot rel) (i j : ι) (ne : i ≠ j)
    (ha : a ∈ (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i) :
    ((decompose' 𝒜 rel a) j).1 = 0 := by
  lift a to (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i using ha
  rw [decompose'_of_ne' 𝒜 rel i j ne a, ZeroMemClass.coe_zero]



#check coe_decompose_mul_of_left_mem_of_not_le
#check DirectSum.coeAddMonoidHom
#check DirectSum.of



lemma decompose'_of (i : ι) (b : (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i) :
   decompose' 𝒜 rel ((DirectSum.coeAddMonoidHom (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜))
     (DirectSum.of _ i b)) = DirectSum.of _ i b := by
  refine DFinsupp.ext fun j ↦ ?_
  obtain rfl | ne := eq_or_ne j i
  · apply Subtype.ext
    rw [decompose'_of_eq]
    · simp
      apply DirectSum.coeAddMonoidHom_of
    · use (choose rel b)
      constructor
      · sorry

      · rw [choose_spec rel b, DirectSum.coeAddMonoidHom_of]


      --exact Subtype.mem _
  · have := of_eq_of_ne
      (β := (fun i ↦ ↥((AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i))) i j b ne.symm
    rw [this, DirectSum.coeAddMonoidHom_of, decompose'_of_ne' _ _ i j ne.symm b]



    --use decompose'_of_ne



  /-let x := inst.decompose' (choose rel a)
  let f : (i : x.support) → ((AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i) :=
    fun i => ⟨RingQuot.mkRingHom rel (x i), by
    obtain ⟨val, property⟩ := i
    simp only [DirectSum.Decomposition.decompose'_eq, Function.comp_apply, AddSubmonoid.mem_map, x]
    simp_all only [DirectSum.Decomposition.decompose'_eq, DFinsupp.mem_support_toFun, ne_eq, x]
    constructor
    · constructor
      on_goal 2 => rfl
      · simp only [SetLike.coe_mem]⟩
  DirectSum.mk (fun i => (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i) x.support f-/


lemma support_subset_decompose' (a : RingQuot rel) : DFinsupp.support (decompose' 𝒜 rel a) ⊆
    DFinsupp.support (inst.decompose' (choose rel a)) := by
  simp [decompose', DirectSum.mk]


lemma decompose'_map_commute (a : RingQuot rel) :
    ∀ x ∈ DFinsupp.support (inst.decompose' (choose rel a)),
    ↑((decompose' 𝒜 rel a) x) =
    (RingQuot.mkRingHom rel) (inst.decompose' ((choose rel a)) x) := by
  intro x hx
  unfold decompose' DirectSum.mk
  simp_all only [DirectSum.Decomposition.decompose'_eq, DFinsupp.mem_support_toFun, ne_eq,
    Function.comp_apply, Finset.coe_sort_coe, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    DFinsupp.mk_apply, not_false_eq_true, ↓reduceDIte, eq_mp_eq_cast, id_eq]
  sorry



instance RingQuotGradedRing : GradedRing ((AddSubmonoid.map (RingQuot.mkRingHom rel)).comp 𝒜) where
  decompose' := decompose' 𝒜 rel
  left_inv a := by
    let b := choose rel a
    have hb : (RingQuot.mkRingHom rel) b = a :=
      Classical.choose_spec <| (RingQuot.mkRingHom_surjective rel) a
    let t := inst.decompose' b
    rw [← DirectSum.sum_support_of (decompose' 𝒜 rel a)]
    have sum := DirectSum.sum_support_of t
    apply_fun (DirectSum.coeAddMonoidHom 𝒜) at sum
    apply_fun (RingQuot.mkRingHom rel) at sum
    simp only [map_sum, DirectSum.coeAddMonoidHom_of] at sum ⊢
    have hat : (RingQuot.mkRingHom rel) ((DirectSum.coeAddMonoidHom 𝒜) t) = a := by
      rw [← hb]
      exact congrArg (⇑(RingQuot.mkRingHom rel)) (inst.left_inv b)
    rw [hat] at sum
    nth_rw 3 [← sum]
    have : ∑ x ∈ DFinsupp.support (decompose' 𝒜 rel a), ((decompose' 𝒜 rel a) x) =
      ∑ x ∈ (DFinsupp.support t : Finset ι), (((decompose' 𝒜 rel a) x) : RingQuot rel) := by
      apply Finset.sum_subset (support_subset_decompose' 𝒜 rel a)
      · intros x _ h
        simp only [Function.comp_apply, DFinsupp.mem_support_toFun, ne_eq, not_not] at h
        exact ZeroMemClass.coe_eq_zero.mpr h
    rw [this]
    apply Finset.sum_congr rfl
    intro x hx
    exact decompose'_map_commute 𝒜 rel a x hx
  right_inv φ := by
    apply φ.induction
    · rw [map_zero, map_zero]
    · intro i b f hfi hb ih
      rw [map_add, map_add, ih]
      have : DFinsupp.single i b = DirectSum.of (fun i ↦ ((AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜) i)) i b := rfl
      rw [this, decompose'_of]

    /- apply DFinsupp.ext
    intro i
    let b := (DirectSum.coeAddMonoidHom (AddSubmonoid.map (RingQuot.mkRingHom rel) ∘ 𝒜)) φ
    let a := choose rel b
    have ha : (RingQuot.mkRingHom rel) a = b :=
      Classical.choose_spec <| (RingQuot.mkRingHom_surjective rel) b
    let t := inst.decompose' a
    have sum := DirectSum.sum_support_of t
    apply_fun (DirectSum.coeAddMonoidHom 𝒜) at sum
    apply_fun (RingQuot.mkRingHom rel) at sum
    simp only [map_sum, DirectSum.coeAddMonoidHom_of] at sum
    have := inst.right_inv t
    have hbt : (RingQuot.mkRingHom rel) ((DirectSum.coeAddMonoidHom 𝒜) t) = b := by
      rw [← ha]
      congr
      sorry
    rw [hbt] at sum
    show decompose' 𝒜 rel b i = φ i
    have eq : (decompose' 𝒜 rel b) i =
      (RingQuot.mkRingHom rel) ↑(t i) := sorry
    rw [← Subtype.coe_inj]
    rw [eq] -/








#check Subtype.coe_inj


end GradedRing

noncomputable section GradedAlgebra

variable {R : Type*} [CommRing R] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [inst : GradedAlgebra 𝒜] (rel : A → A → Prop)

local instance : (i : ι) → (x : ↥(𝒜 i)) → Decidable (x ≠ 0) :=
    fun _ x ↦ Classical.propDecidable (x ≠ 0)



abbrev Algchoose (R : Type*) [CommRing R] [Algebra R A] (a : RingQuot rel)  :=
  Classical.choose <| (RingQuot.mkAlgHom_surjective R rel) a



/-- The `Algdecompose'` argument of `RingQuotGradedAlgebra`. -/
def Algdecompose' := fun a : RingQuot rel =>
  let x := inst.decompose' (Algchoose rel R a)
  let f : (i : x.support) → ((Submodule.map (RingQuot.mkAlgHom R rel) ∘ 𝒜) i) :=
    fun i => ⟨RingQuot.mkAlgHom R rel (x i), by
    obtain ⟨val, property⟩ := i
    simp only [DirectSum.Decomposition.decompose'_eq, Function.comp_apply, Submodule.mem_map, x]
    simp_all only [DirectSum.Decomposition.decompose'_eq, DFinsupp.mem_support_toFun, ne_eq, x]
    constructor
    · constructor
      on_goal 2 => rfl
      · simp only [SetLike.coe_mem]⟩
  DirectSum.mk (fun i => (Submodule.map (RingQuot.mkAlgHom R rel) ∘ 𝒜) i) x.support f


lemma support_subset_Algdecompose' (a : RingQuot rel) : DFinsupp.support (Algdecompose' 𝒜 rel a) ⊆
    DFinsupp.support (inst.decompose' (Algchoose rel R a)) := by
  unfold Algdecompose' DirectSum.mk
  simp only [Function.comp_apply, DirectSum.Decomposition.decompose'_eq, Finset.coe_sort_coe,
  eq_mpr_eq_cast, cast_eq, AddMonoidHom.coe_mk, ZeroHom.coe_mk, DFinsupp.support_mk_subset]



lemma Algdecompose'_map_commute (a : RingQuot rel) :
    ∀ x ∈ DFinsupp.support (inst.decompose' (Algchoose rel R a)),
    ↑((Algdecompose' 𝒜 rel a) x) =
    (RingQuot.mkAlgHom R rel) (inst.decompose' (Algchoose rel R a) x) := by
  intro x hx
  unfold Algdecompose' DirectSum.mk
  simp_all only [DirectSum.Decomposition.decompose'_eq, DFinsupp.mem_support_toFun, ne_eq,
    Function.comp_apply, Finset.coe_sort_coe, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    DFinsupp.mk_apply, not_false_eq_true, ↓reduceDIte, eq_mp_eq_cast, id_eq]


variable [IsHomogeneousRelation 𝒜 rel]


instance RingQuotGradedAlgebra :
    GradedAlgebra ((Submodule.map (RingQuot.mkAlgHom R rel)).comp 𝒜) where
  one_mem := by
    use 1
    constructor
    · exact SetLike.GradedOne.one_mem
    · exact map_one (RingQuot.mkAlgHom R rel)
  mul_mem := by
    intro x y gi gj hi hj
    simp only [Function.comp_apply, Submodule.mem_map]
    rcases hi with ⟨a, ha1, ha2⟩
    rcases hj with ⟨b, hb1, hb2⟩
    use a * b
    constructor
    · exact SetLike.GradedMul.mul_mem ha1 hb1
    · rw [map_mul, ha2, hb2]
  decompose' := Algdecompose' 𝒜 rel
  left_inv a := by
    let b := Algchoose rel R a
    have hb : (RingQuot.mkAlgHom R rel) b = a :=
      Classical.choose_spec $ (RingQuot.mkAlgHom_surjective R rel) a
    let t := inst.decompose' b
    rw [← DirectSum.sum_support_of (Algdecompose' 𝒜 rel a)]
    have sum := DirectSum.sum_support_of t
    apply_fun (DirectSum.coeAddMonoidHom 𝒜) at sum
    apply_fun (RingQuot.mkAlgHom R rel) at sum
    simp only [map_sum, DirectSum.coeAddMonoidHom_of] at sum ⊢
    have hat : (RingQuot.mkAlgHom R rel) ((DirectSum.coeAddMonoidHom 𝒜) t) = a := by
      rw [← hb]
      exact congrArg (⇑(RingQuot.mkAlgHom R rel)) (inst.left_inv b)
    rw [hat] at sum
    nth_rw 3 [← sum]
    have : ∑ x ∈ DFinsupp.support (Algdecompose' 𝒜 rel a), ((Algdecompose' 𝒜 rel a) x) =
      ∑ x ∈ (DFinsupp.support t : Finset ι), (((Algdecompose' 𝒜 rel a) x) : RingQuot rel) := by
      apply Finset.sum_subset (support_subset_Algdecompose' 𝒜 rel a)
      · intros x _ h
        simp only [Function.comp_apply, DFinsupp.mem_support_toFun, ne_eq, not_not] at h
        exact ZeroMemClass.coe_eq_zero.mpr h
    rw [this]
    apply Finset.sum_congr rfl
    intro x hx
    exact Algdecompose'_map_commute 𝒜 rel a x hx

  right_inv := by
    sorry

end GradedAlgebra

end HomogeneousRelation
