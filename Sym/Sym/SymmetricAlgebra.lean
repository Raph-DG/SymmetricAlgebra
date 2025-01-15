import Mathlib
import Sym.newHomogeneousRelation

open MvPolynomial RingQuot

noncomputable section
variable (R : Type*) [CommRing R]
variable (L : Type*) [AddCommMonoid L] [Module R L]
local notation "ι" => TensorAlgebra.ι R

-- def I := TwoSidedIdeal.span {(ιₜ x * ιₜ y - ιₜ y * ιₜ x) | (x : L) (y : L)}

inductive SymRel : (TensorAlgebra R L) → (TensorAlgebra R L) → Prop where
  | mul_comm (x y : L) : SymRel (ι x * ι y) (ι y * ι x)


instance : IsHomogeneousRelation (fun (n : ℕ) ↦ (LinearMap.range (ι : L →ₗ[R] TensorAlgebra R L) ^ n)) (SymRel R L) :=⟨ by
  have h_iota (x y : L) : (ι x * ι y) ∈ (fun (n : ℕ) ↦ (LinearMap.range (ι : L →ₗ[R] TensorAlgebra R L) ^ n)) 2 := by
    simp only [pow_two]; apply Submodule.mul_mem_mul; simp; simp
  intro x y h i
  induction h
  case mul_comm x y =>
    have : (SymRel R L) (ι x * ι y) (ι y * ι x) := by apply SymRel.mul_comm x y
    have h_decompose : (ι x * ι y) = ((DirectSum.decompose (fun n ↦ LinearMap.range ι ^ n) (ι x * ι y)) 2) := by
        exact
          Eq.symm (DirectSum.decompose_of_mem_same (fun n ↦ LinearMap.range ι ^ n) (h_iota x y))
    have h_decompose' : (ι y * ι x) = ((DirectSum.decompose (fun n ↦ LinearMap.range ι ^ n) (ι y * ι x)) 2) := by
        exact
          Eq.symm (DirectSum.decompose_of_mem_same (fun n ↦ LinearMap.range ι ^ n) (h_iota y x))
    have h_zero : ∀ i ≠ 2, (GradedRing.proj (fun (n : ℕ) ↦ (LinearMap.range (ι : L →ₗ[R] TensorAlgebra R L) ^ n)) i (ι x * ι y)) = 0 := by
      intro i h
      rw [GradedRing.proj_apply, h_decompose]
      simp only [DirectSum.decompose_coe, ZeroMemClass.coe_eq_zero]
      apply DirectSum.of_eq_of_ne
      exact id (Ne.symm h)
    have h_zero' : ∀ i ≠ 2, (GradedRing.proj (fun (n : ℕ) ↦ (LinearMap.range (ι : L →ₗ[R] TensorAlgebra R L) ^ n)) i (ι y * ι x)) = 0 := by
      intro i h
      rw [GradedRing.proj_apply, h_decompose']
      simp only [DirectSum.decompose_coe, ZeroMemClass.coe_eq_zero]
      apply DirectSum.of_eq_of_ne
      exact id (Ne.symm h)
    by_cases h0 : i = 2
    · constructor
      rw [h0]
      simp only [GradedRing.proj_apply]
      rw [←h_decompose, ←h_decompose']
      exact this
    · rw [←ne_eq] at h0
      constructor
      have h_zeroh : (GradedRing.proj (fun (n : ℕ) ↦ (LinearMap.range (ι : L →ₗ[R] TensorAlgebra R L) ^ n)) i (ι x * ι y)) = 0 := by exact h_zero i h0
      have h_zeroh' : (GradedRing.proj (fun (n : ℕ) ↦ (LinearMap.range (ι : L →ₗ[R] TensorAlgebra R L) ^ n)) i (ι y * ι x)) = 0 := by exact h_zero' i h0
      rw [h_zeroh, h_zeroh']
      have zero : 0 = (ι (0 : L) * ι (0 : L)) := by simp only [map_zero, mul_zero]
      rw [zero]
      exact SymRel.mul_comm 0 0
⟩

abbrev SymmetricAlgebra := RingQuot (SymRel R L)


variable {R} {L} in
structure IsSymAlg {RL : Type*}
              [CommRing RL] [a : Algebra R RL]
              (iota : L →ₗ[R] RL) : Prop where
  ex_map {A : Type*} [CommRing A] [a : Algebra R A] (φ : L →ₗ[R] A)
    : ∃! φ' : RL →ₐ[R] A, φ = φ' ∘ₗ iota







local notation "𝔖" => SymmetricAlgebra



namespace SymmetricAlgebra

-- This is lemma 1
instance : CommRing (𝔖 R L) where
  mul_comm a b := match a, b with
    | ⟨a⟩, ⟨b⟩ => by
      apply Quot.ind _ a; apply Quot.ind _ b; intro a b;
      rw [mul_quot, mul_quot]
      suffices h : ∀ (x : TensorAlgebra R L), (⟨Quot.mk (RingQuot.Rel (SymRel R L)) (x * a)⟩ : (RingQuot (SymRel R L))) = ⟨Quot.mk (RingQuot.Rel (SymRel R L)) (a * x)⟩ by
        exact (h b)
      let P : TensorAlgebra R L → TensorAlgebra R L → Prop := fun x y ↦ (⟨Quot.mk (RingQuot.Rel (SymRel R L)) (x * y)⟩ : (RingQuot (SymRel R L))) = ⟨Quot.mk (RingQuot.Rel (SymRel R L)) (y * x)⟩
      have P_smul (r : R) (x : TensorAlgebra R L) : P x (algebraMap R (TensorAlgebra R L) r) := by
        unfold P; rw [Algebra.commutes]
      have P_mul (x y z : TensorAlgebra R L) (h1 : P z x) (h2 : P z y) : P z (x * y) := by
        unfold P at h1 h2 ⊢
        rw [← mul_quot, ← mul_quot, ← mul_quot, ← mul_quot, ← mul_assoc, mul_quot, h1, ← mul_quot, mul_assoc, mul_quot, h2, ← mul_quot, mul_assoc]
      have P_add (x y z : TensorAlgebra R L) (h1 : P z x) (h2 : P z y) : P z (x + y) := by
        unfold P at h1 h2 ⊢
        rw [mul_add, add_mul, ← add_quot, ← add_quot, h1, h2]
      have P_symm {x y : TensorAlgebra R L} (h : P x y) : P y x := h.symm
      have P_base (x y : L) : P (ι x) (ι y) := by
        unfold P
        rw [Quot.sound (Rel.of (SymRel.mul_comm x y))]
      apply TensorAlgebra.induction (C := fun y ↦ ∀ (x : TensorAlgebra R L), P x y) _ _ _ _ a
      · intro r; exact P_smul r
      · intro x; apply TensorAlgebra.induction
        · intro r; exact P_symm (P_smul r (ι x))
        · intro y; exact P_base y x
        · intro a1 a2 h1 h2; exact P_symm (P_mul a1 a2 (ι x) (P_symm h1) (P_symm h2))
        · intro a1 a2 h1 h2; exact P_symm (P_add a1 a2 (ι x) (P_symm h1) (P_symm h2))
      · intro a1 a2 h1 h2 x; exact P_mul a1 a2 x (h1 x) (h2 x)
      · intro a1 a2 h1 h2 x; exact P_add a1 a2 x (h1 x) (h2 x)

--#check IsSymAlg (𝔖 R L)

abbrev mkAlgHom : TensorAlgebra R L →ₐ[R] 𝔖 R L := RingQuot.mkAlgHom R (SymRel R L)

def iota : L →ₗ[R] 𝔖 R L := (mkAlgHom R L).toLinearMap.comp (TensorAlgebra.ι R (M := L))


/-
This says that the symmetric algebra over R of the zero module
(here defined as any module which has at most one element) must be isomorphic
as an R algebra to R.
-/
def symAlgOfZeroModule {RZ M : Type*} [CommRing RZ] [a : Algebra R RZ]
  [AddCommMonoid M] [Module R M] (hm : Subsingleton M) : IsSymAlg (R := R) (L := M) (RL := R) 0 := {
    ex_map := by
      intro a b c φ

      -- R is initial in the category of R-algebras, so this morphism is unique
      let φ' : R →ₐ[R] a := sorry
      use φ'
      constructor
      · -- Prove relation holds
        sorry
      · -- Prove uniqueness (should hold by definition)
        sorry
  }



/-
Use TensorAlgebra.lift and RingQuot.lift for existence and TensorAlgebra.lift_unique
for uniqueness
-/
def lem2 : IsSymAlg (iota R L) where
  ex_map := by
    intro alg com halg φ
    let tensorphi : TensorAlgebra R L →ₐ[R] alg := TensorAlgebra.lift R φ

    -- Define a morphism out of the symmetric algebra using RingQuot.lift
    let φ' : SymmetricAlgebra R L →ₐ[R] alg :=
      let ah := RingQuot.mkAlgHom R (SymRel R L)

      let lifter := (RingQuot.liftAlgHom (S := R) (s := SymRel R L) (B := alg)).toFun
      --convert lifter



      let res : ∀ ⦃x y : TensorAlgebra R L⦄, SymRel R L x y → tensorphi x = tensorphi y := by
        intro x y h
        induction h
        case mul_comm x y =>
          simp only [map_mul]
          rw [@NonUnitalCommSemiring.mul_comm]

      lifter ⟨tensorphi, res⟩



    use φ'
    constructor
    · -- Prove existence
      simp only
      sorry
    · -- Prove uniqueness
      intro g
      simp only
      intro hg
      apply AlgHom.ext
      intro x
      -- unfold φ'
      sorry


/-
Any two morphisms iM : M →ₗ[R] RM and iM' : M →ₗ[R] RM' both satisfying isSymAlg must
have that RM and RM' are isomorphic
-/
def IsSymAlgIsoInvariant {M : Type*} [AddCommMonoid M] [Module R M]
         {RM RM' : Type*}
         [CommRing RM] [Algebra R RM] [CommRing RM'] [Algebra R RM']
         {iM : M →ₗ[R] RM} {iM' : M →ₗ[R] RM'} (salg : IsSymAlg iM) (salg' : IsSymAlg iM')
         : RM ≃ₐ[R] RM' := sorry




def IsSymAlg.lift {M M' : Type*} [AddCommMonoid M] [Module R M]
         {RM : Type*}
         [CommRing RM] [a : Algebra R RM] [CommRing M'] [Algebra R M']
         {iM : M →ₗ[R] RM} (salg : IsSymAlg iM) (phi : M →ₗ[R] M') : RM →ₐ[R] M' :=
  (salg.ex_map phi).exists.choose


theorem IsSymAlg.liftCorrect {M M' : Type*} [AddCommMonoid M] [Module R M]
         {RM : Type*}
         [CommRing RM] [a : Algebra R RM] [CommRing M'] [Algebra R M']
         {iM : M →ₗ[R] RM} (salg : IsSymAlg iM) (phi : M →ₗ[R] M') :
         ((IsSymAlg.lift R salg phi) ∘ₗ iM) = phi := sorry


def freeRkOneToPoly {M : Type*} [AddCommGroup M] [Module R M]
  [Nontrivial R] (mf : Module.Free R M)
  (r1 : Module.finrank R M = 1) : M →ₗ[R] Polynomial R :=
    have : Module.Finite R M := Module.finite_of_finrank_eq_succ r1
    let B := Module.finBasis R M
    Basis.constr B R (fun _ ↦ Polynomial.X)
/-


Use Polynomial.aeval to construct an alegbra morphism from Polynomial R to A sending
x to φ(e), where is a . We then wish to show that this morphism and the morphism constructed in=
the previous paragraph are inverses of one another

You may need to use Polynomial.algHom_ext in order to prove things about equivalences
between maps out of Polynomial R
-/
def lem3 {M : Type*} [AddCommGroup M] [Module R M] (mf : Module.Free R M)
             (r1 : Module.finrank R M = 1) [Nontrivial R]
             : IsSymAlg (freeRkOneToPoly R mf r1) := {
    ex_map := by
      intro A rA aA φ
      have : Module.Finite R M := Module.finite_of_finrank_eq_succ r1
      let B := Module.finBasis R M
      -- Take e to be the unique element of our basis B

      let idx : Fin (Module.finrank R M) := Fin.mk 0 (by rw [r1]; exact Nat.zero_lt_one)
      let e : M := B idx
      -- Use Polynomial.aeval to define a morphism φ' : Polynomial R →ₐ[R] A which
      -- takes X and maps it to φ(e)
      let φ' : Polynomial R →ₐ[R] A := Polynomial.aeval (φ e)

      use φ'
      constructor
      · simp only
        have (x : M) : ∃ (y : R), x = y • e := by
          use (B.repr x) (Fin.mk 0 (by rw [r1]; exact Nat.zero_lt_one))
          rw [← B.sum_repr x, Finset.sum_eq_single (Fin.mk 0 (by rw [r1]; exact Nat.zero_lt_one))]
          · simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
            Finsupp.single_eq_same]
          · intro i hi1 hi2
            have this :  i = idx := by
              have : Fintype.card (Fin (Module.finrank R M)) ≤ 1 := by
                simp only [Fintype.card_fin]
                exact Nat.le_of_eq r1
              apply Fintype.card_le_one_iff.mp this
            have this' : i ≠ idx := by exact hi2
            contradiction
          · intro h
              refine
                smul_eq_zero_of_right
                  ((B.repr x) ⟨0, Eq.mpr (id (congrArg (fun _a ↦ 0 < _a) r1)) Nat.zero_lt_one⟩) ?_
              apply Basis.apply_eq_iff.mpr
              simp only [map_zero]
              sorry
          -- have : (B.repr x) (Fin.mk 0 (by rw [r1]; exact Nat.zero_lt_one)) = 1 := by
          --   rw [← B.sum_repr x, Finset.sum_eq_single (Fin.mk 0 (by rw [r1]; exact Nat.zero_lt_one))]
          --   · simp only


          --     have this' : i ≠ idx := by exact hi2
          --     contradiction

        rw [@LinearMap.ext_iff]
        intro x
        specialize this x
        rcases this with ⟨y, hy⟩
        rw [hy]
        simp only [map_smul, LinearMap.coe_comp, LieHom.coe_toLinearMap, AlgHom.coe_toLieHom,
          Function.comp_apply]
        have: φ e = φ' ((freeRkOneToPoly R mf r1) e) := by
          have : Polynomial.X = (freeRkOneToPoly R mf r1) e := by
            unfold freeRkOneToPoly
            simp only [Polynomial.aeval_X]
            exact Eq.symm (Basis.constr_basis (Module.finBasis R M) R (fun x ↦ Polynomial.X) idx)
          rw [←this]
          exact Eq.symm (Polynomial.aeval_X (φ e))
        rw [this]

      · intro g
        simp
        intro hg
        -- Here, use Polynomial.algHom_ext to prove uniqueness
        apply Polynomial.algHom_ext
        have : φ' Polynomial.X = φ e := by exact Polynomial.aeval_X (φ e)
        have this': g Polynomial.X = φ e := by
          rw [hg]
          simp only [LinearMap.coe_comp, LieHom.coe_toLinearMap, AlgHom.coe_toLieHom,
            Function.comp_apply]
          apply AlgHom.congr_arg
          have : (freeRkOneToPoly R mf r1) e = Basis.constr B R (fun _ ↦ Polynomial.X) e := by
            simp [freeRkOneToPoly, Basis.constr]
          rw [this]
          exact Eq.symm (Basis.constr_basis B R (fun x ↦ Polynomial.X) idx)
        rw [this, this']
  }

  /-
  { toFun := f
    map_one' := f.map_one
    map_mul' := f.map_mul
    map_zero' := f.map_zero
    map_add' := f.map_add }-/

/-
Functoriality: Take iM' ∘ phi to get a map from M to R[M'], then use the universal
property to lift this to a map from R[M] to R[M']
-/
def lem5 {M M' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
         {RM RM' : Type*}
         [CommRing RM] [a : Algebra R RM] [CommRing RM'] [a : Algebra R RM']
         {iM : M →ₗ[R] RM} {iM' : M' →ₗ[R] RM'} (salg : IsSymAlg iM)
         (salg' : IsSymAlg iM') (phi : M →ₗ[R] M') : RM →ₐ[R] RM' :=
    IsSymAlg.lift R salg (iM'.comp phi)

-- Define the natural map from RM₁ ⊗[R] RM₂ to RM defined
open TensorProduct
def lem6Map {M₁ M₂ : Type*}
            [AddCommMonoid M₁] [Module R M₁]
            [AddCommMonoid M₂] [Module R M₂]
         {RM RM₁ RM₂ : Type*}
         [CommRing RM] [Algebra R RM] [CommRing RM₁] [Algebra R RM₁]
         [CommRing RM₂] [Algebra R RM₂]
         {iM : M₁ × M₂ →ₗ[R] RM} {iM₁ : M₁ →ₗ[R] RM₁} {iM₂ : M₂ →ₗ[R] RM₂}
         (salg : IsSymAlg iM) (salg₁ : IsSymAlg iM₁) (salg₂ : IsSymAlg iM₂)
         : RM₁ ⊗[R] RM₂ →ₐ[R] RM :=

    sorry
-- variable {R} {L} in
-- structure IsSymAlg {RL : Type*}
--               [CommRing RL] [a : Algebra R RL]
--               (iota : L →ₗ[R] RL) : Prop where
--   ex_map {A : Type*} [CommRing A] [a : Algebra R A] (φ : L →ₗ[R] A)
--     : ∃! φ' : RL →ₐ[R] A, φ = φ' ∘ iota



variable (I : Type*) (basis_I : Basis I R L)

def basisToPoly : L →ₗ[R] MvPolynomial I R :=
    Basis.constr basis_I R (fun i ↦ MvPolynomial.X i)

/-
This should be a more conceptual version of the proof below
-/
def cor1 : IsSymAlg (basisToPoly R L I basis_I) := {
  ex_map := by

    sorry
}


def symmetric_algebra_iso_mv_polynomial : MvPolynomial I R ≃ₐ[R] 𝔖 R L :=
  AlgEquiv.ofAlgHom
    ⟨eval₂Hom (algebraMap R (𝔖 R L)) (fun i ↦ mkRingHom _ (ι (basis_I i))), fun _ ↦ eval₂_C _ _ _⟩
    (liftAlgHom R ⟨TensorAlgebra.lift R ((Finsupp.linearCombination R (fun (i : I) ↦ ((X i) : MvPolynomial I R))).comp basis_I.repr.1), fun {u v} h ↦ match h with | SymRel.mul_comm x y => by simp [mul_comm]⟩)
    (by
      apply ringQuot_ext'; apply TensorAlgebra.hom_ext; apply Basis.ext basis_I; intro i
      simp [SymmetricAlgebra]; rw [RingQuot.mkAlgHom, AlgHom.coe_mk])
    (by
      apply algHom_ext; intro i
      simp only [AlgHom.coe_comp, AlgHom.coe_mk, coe_eval₂Hom, Function.comp_apply, eval₂_X,
        AlgHom.coe_id, id_eq]
      have h1 : (mkRingHom (SymRel R L)) (ι (basis_I i)) = (RingQuot.mkAlgHom R (SymRel R L)) (ι (basis_I i)) := by rw [RingQuot.mkAlgHom, AlgHom.coe_mk]
      have h2 : ((TensorAlgebra.lift R) ((Finsupp.linearCombination R fun i => (X i : MvPolynomial I R)) ∘ₗ basis_I.repr.1)) (ι (basis_I i)) = X i := by simp
      rw [← h2, h1]
      apply liftAlgHom_mkAlgHom_apply)

abbrev gradingSymmetricAlgebra : ℕ → Submodule R (𝔖 R L) :=
  (Submodule.map (mkAlgHom R L)).comp
    (LinearMap.range (TensorAlgebra.ι R : L →ₗ[R] TensorAlgebra R L) ^ ·)


#synth GradedAlgebra (gradingSymmetricAlgebra R L)

lemma proj_comm (x : TensorAlgebra R L) (m : ℕ) : mkAlgHom R L ((GradedAlgebra.proj ((LinearMap.range (TensorAlgebra.ι R : L →ₗ[R] TensorAlgebra R L) ^ ·)) m) x) = (GradedAlgebra.proj (gradingSymmetricAlgebra R L) m) (mkAlgHom R L x) := by
  sorry
