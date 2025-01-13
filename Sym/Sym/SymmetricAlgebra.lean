import Mathlib
import Sym.newHomogeneousRelation

open MvPolynomial RingQuot

noncomputable section
variable (R : Type*) [CommRing R]
variable (L : Type*) [AddCommMonoid L] [Module R L]
local notation "ι" => TensorAlgebra.ι R

-- def I := TwoSidedIdeal.span {(ιₜ x * ιₜ y - ιₜ y * ιₜ x) | (x : L) (y : L)}

inductive SymRel : (TensorAlgebra R L) → (TensorAlgebra R L) → Prop :=
  | mul_comm (x y : L) : SymRel (ι x * ι y) (ι y * ι x)


instance : IsHomogeneousRelation (fun (n : ℕ) ↦ (LinearMap.range (ι : L →ₗ[R] TensorAlgebra R L) ^ n)) (SymRel R L) := ⟨by
  have h_iota (x : L) : (ι x) ∈ (fun (n : ℕ) ↦ (LinearMap.range (ι : L →ₗ[R] TensorAlgebra R L) ^ n)) 1 := by
    simp only [pow_one, LinearMap.mem_range, TensorAlgebra.ι_inj, exists_eq]
  have h_iota2 (x y : L) : (ι x * ι y) ∈ (fun (n : ℕ) ↦ (LinearMap.range (ι : L →ₗ[R] TensorAlgebra R L) ^ n)) 2 := by
    simp only [pow_two]; apply Submodule.mul_mem_mul; simp; simp
  intro x y h; induction h
  case mul_comm x y =>
    sorry
⟩

abbrev SymmetricAlgebra := RingQuot (SymRel R L)


variable {R} {L} in
structure IsSymAlg {RL : Type*}
              [CommRing RL] [a : Algebra R RL]
              (iota : L →ₗ[R] RL) : Prop where
  ex_map {A : Type*} [CommRing A] [a : Algebra R A] (φ : L →ₗ[R] A)
    : ∃! φ' : RL →ₐ[R] A, φ = φ' ∘ iota







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
Use TensorAlgebra.lift and RingQuot.lift for existence and TensorAlgebra.lift_unique
for uniqueness
-/
def lem2 : IsSymAlg (iota R L) := by
  sorry


/-
Define a map from M to Polynomial R by sending e to x, where e is r1.symm 1. Then
use the universal property described in IsSymRel to lift this to a morphism from R[M]
to Polynomial R.

Then use Polynomial.aeval to construct an alegbra morphism from R[x] to R[M] sending
x to ι(e). We then wish to show that this morphism and the morphism constructed in=
the previous paragraph are inverses of one another

You may need to use Polynomial.algHom_ext in order to prove things about equivalences
between maps out of Polynomial R
-/
def lem3 {M : Type*} [AddCommMonoid M] [Module R M] (mf : Module.Free R M)
             (r1 : Module.finrank M = 1)
             {SA : Type*} [CommRing SA] [a : Algebra R SA] {inj : M →ₗ[R] SA}
             (salg : IsSymAlg inj)
             : SA ≃ₐ[R] Polynomial R := by


  sorry


/-
Functoriality: Take iM' ∘ phi to get a map from M to R[M'], then use the universal
property to lift this to a map from R[M] to R[M']
-/
def lem5 {M M' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
         {RM RM' : Type*}
         [CommRing RM] [a : Algebra R RM] [CommRing RM'] [a : Algebra R RM']
         {iM : M →ₗ[R] RM} {iM' : M' →ₗ[R] RM'} (salg : IsSymAlg iM)
         (salg : IsSymAlg iM') (phi : M →ₗ[R] M') : RM →+* RM' := sorry

variable (I : Type*) (basis_I : Basis I R L)

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
