import Mathlib
import Sym.newHomogeneousRelation
import Aesop

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
  ex_map {A : Type*} [CommRing A] [Algebra R A] (φ : L →ₗ[R] A)
    : ∃! φ' : RL →ₐ[R] A, φ = φ'.toLinearMap ∘ₗ iota
  ex_map_self (φ : L →ₗ[R] RL) : ∃! φ' : RL →ₐ[R] RL, φ = φ'.toLinearMap ∘ₗ iota






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
def symAlgOfZeroModule {RZ M : Type*} [CommRing RZ] [Algebra R RZ]
  [AddCommMonoid M] [Module R M] (hm : Subsingleton M) : IsSymAlg (R := R) (L := M) (RL := R) 0 := {
    ex_map := by
      intro a b c φ
      have hφ : φ = 0 := by exact Subsingleton.eq_zero φ
      -- R is initial in the category of R-algebras, so this morphism is unique
      let φ' : R →ₐ[R] a := Algebra.ofId R a
      use φ'
      constructor
      · -- Prove relation holds
        rw [hφ]
        ext x
        simp only [LinearMap.zero_apply, LinearMap.comp_zero]
      · -- Prove uniqueness (should hold by definition)
         intro ψ hψ
         exact Algebra.ext_id_iff.mpr trivial
    ex_map_self := by
      intro φ
      have hφ : φ = 0 := by exact Subsingleton.eq_zero φ
      -- R is initial in the category of R-algebras, so this morphism is unique
      let φ' : R →ₐ[R] R := Algebra.ofId R R
      use φ'
      constructor
      · -- Prove relation holds
        rw [hφ]
        ext x
        simp only [LinearMap.zero_apply, LinearMap.comp_zero]
      · -- Prove uniqueness (should hold by definition)
         intro ψ hψ
         exact Algebra.ext_id_iff.mpr trivial
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
    let res : ∀ ⦃x y : TensorAlgebra R L⦄, SymRel R L x y → tensorphi x = tensorphi y := by
        intro x y h
        induction h
        case mul_comm x y =>
          simp only [map_mul]
          rw [@NonUnitalCommSemiring.mul_comm]

    use (RingQuot.liftAlgHom (S := R) (s := SymRel R L) (B := alg)) ⟨TensorAlgebra.lift R φ, res⟩
    constructor
    · unfold iota
      have teneq := TensorAlgebra.lift.eq_1 (M := L) (A := alg) R
      have quoteq := RingQuot.eq_liftAlgHom_comp_mkAlgHom R (TensorAlgebra.lift R φ)
      ext a
      simp
    · intro a b
      apply RingQuot.liftAlgHom_unique
      exact
        (TensorAlgebra.lift_unique φ (a.comp (RingQuot.mkAlgHom R (SymRel R L)))).mp
          (id (Eq.symm b))
  ex_map_self := by
    intro φ
    let tensorphi : TensorAlgebra R L →ₐ[R] 𝔖 R L:= TensorAlgebra.lift R φ

    -- Define a morphism out of the symmetric algebra using RingQuot.lift
    let res : ∀ ⦃x y : TensorAlgebra R L⦄, SymRel R L x y → tensorphi x = tensorphi y := by
        intro x y h
        induction h
        case mul_comm x y =>
          simp only [map_mul]
          rw [@NonUnitalCommSemiring.mul_comm]

    use (RingQuot.liftAlgHom (S := R) (s := SymRel R L) (B := 𝔖 R L)) ⟨TensorAlgebra.lift R φ, res⟩
    constructor
    · unfold iota
      have teneq := TensorAlgebra.lift.eq_1 (M := L) (A := 𝔖 R L) R
      have quoteq := RingQuot.eq_liftAlgHom_comp_mkAlgHom R (TensorAlgebra.lift R φ)
      ext a
      simp
    · intro a b
      apply RingQuot.liftAlgHom_unique
      exact
        (TensorAlgebra.lift_unique φ (a.comp (RingQuot.mkAlgHom R (SymRel R L)))).mp
          (id (Eq.symm b))

 def IsSymAlg.lift {M M' : Type*} [AddCommMonoid M] [Module R M]
         {RM : Type*}
         [CommRing RM] [Algebra R RM] [CommRing M'] [Algebra R M']
         {iM : M →ₗ[R] RM} (salg : IsSymAlg iM) (phi : M →ₗ[R] M') : RM →ₐ[R] M' :=
  (salg.ex_map phi).choose

/-
Any two morphisms iM : M →ₗ[R] RM and iM' : M →ₗ[R] RM' both satisfying isSymAlg must
have that RM and RM' are isomorphic
-/

theorem IsSymAlg.lift_spec {M M' : Type*} [AddCommMonoid M] [Module R M]
         {RM : Type*}
         [CommRing RM] [Algebra R RM] [CommRing M'] [Algebra R M']
         {iM : M →ₗ[R] RM} (salg : IsSymAlg iM) (phi : M →ₗ[R] M')
         : phi = (IsSymAlg.lift _ salg phi).toLinearMap ∘ₗ iM := by
  exact (salg.ex_map phi).choose_spec.1

theorem IsSymAlg.comp_spec {M : Type*} [AddCommMonoid M] [Module R M]
         {RM RM' : Type*}
         [CommRing RM] [Algebra R RM] [CommRing RM'] [Algebra R RM']
         {iM : M →ₗ[R] RM} {iM' : M →ₗ[R] RM'} (salg : IsSymAlg iM) (salg' : IsSymAlg iM'):
  iM = ((AlgHom.comp (IsSymAlg.lift _ salg' iM) (IsSymAlg.lift _ salg iM')).toLinearMap) ∘ₗ iM := by
  rw [AlgHom.comp_toLinearMap]
  rw [LinearMap.comp_assoc]
  rw [← IsSymAlg.lift_spec _ salg iM']
  exact IsSymAlg.lift_spec _ salg' iM

def IsSymAlgIsoInvariant {M : Type*} [AddCommMonoid M] [Module R M]
         {RM RM' : Type*}
         [CommRing RM] [Algebra R RM] [CommRing RM'] [Algebra R RM']
         {iM : M →ₗ[R] RM} {iM' : M →ₗ[R] RM'} (salg : IsSymAlg iM) (salg' : IsSymAlg iM')
         : RM ≃ₐ[R] RM' where
    toFun : RM →ₐ[R] RM' := IsSymAlg.lift R salg iM'
    invFun : RM' →ₐ[R] RM := IsSymAlg.lift R salg' iM
    -- Prove these properties using the universal property
    left_inv := by
      rw [@Function.leftInverse_iff_comp]
      let φ := IsSymAlg.lift R salg iM'
      let ψ := IsSymAlg.lift R salg' iM

      have h1 : iM' = φ ∘ₗ iM := (salg.ex_map iM').choose_spec.1
      have h2 : iM = ψ ∘ₗ iM' := (salg'.ex_map iM).choose_spec.1
      have h3 : ((AlgHom.comp ψ φ).toLinearMap) ∘ iM = (AlgHom.id R RM).toLinearMap ∘ₗ iM := by
        nth_rw 2 [h2]
        rw [h1]
        simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, AlgHom.toLinearMap_id,
          LinearMap.id_comp, LieHom.coe_toLinearMap, AlgHom.coe_toLieHom]
        exact rfl

      have comp_spec := IsSymAlg.comp_spec _ salg salg'
      -- Both φ' ∘ φ and id satisfy the property from ex_map_self
      have prop1 : iM = (AlgHom.comp ψ φ).toLinearMap ∘ₗ iM := by exact comp_spec
      have prop2 : iM = (AlgHom.id R RM).toLinearMap ∘ₗ iM := by exact rfl

      -- Use uniqueness to conclude they are equal
      have h_unique := (salg.ex_map_self iM).unique prop1 prop2
      --exact h_unique ▸ (AlgHom.id_apply R RM x)
      have eq: (AlgHom.comp ψ φ) = (AlgHom.id R RM) := by exact h_unique
      unfold φ ψ at eq
      have : (AlgHom.id R RM) = (id : RM → RM) := by rfl
      have this1 : ⇑(IsSymAlg.lift R salg' iM) ∘ ⇑(IsSymAlg.lift R salg iM') = (AlgHom.comp ψ φ) := by rfl
      rw [←this, this1, eq]

    right_inv := by
      rw [@Function.rightInverse_iff_comp]
      let φ := IsSymAlg.lift R salg iM'
      let ψ := IsSymAlg.lift R salg' iM
      have h1 : iM' = φ ∘ₗ iM := (salg.ex_map iM').choose_spec.1
      have h2 : iM = ψ ∘ₗ iM' := (salg'.ex_map iM).choose_spec.1
      have h3 : ((AlgHom.comp φ ψ).toLinearMap) ∘ iM' = (AlgHom.id R RM').toLinearMap ∘ₗ iM' := by
        nth_rw 2 [h1]
        rw [h2]
        simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, AlgHom.toLinearMap_id,
          LinearMap.id_comp, LieHom.coe_toLinearMap, AlgHom.coe_toLieHom]
        rfl

      have comp_spec := IsSymAlg.comp_spec _ salg' salg
      -- Both φ' ∘ φ and id satisfy the property from ex_map_self
      have prop1 : iM' = (AlgHom.comp φ ψ).toLinearMap ∘ₗ iM' := by exact comp_spec
      have prop2 : iM' = (AlgHom.id R RM').toLinearMap ∘ₗ iM' := by exact rfl

      -- Use uniqueness to conclude they are equal
      have h_unique := (salg'.ex_map_self iM').unique prop1 prop2
      --exact h_unique ▸ (AlgHom.id_apply R RM x)
      have eq: (AlgHom.comp φ ψ) = (AlgHom.id R RM') := by exact h_unique
      unfold φ ψ at eq
      have : (AlgHom.id R RM') = (id : RM' → RM') := by rfl
      have this1 : ⇑(IsSymAlg.lift R salg iM') ∘ ⇑(IsSymAlg.lift R salg' iM) = (AlgHom.comp φ ψ) := by rfl
      rw [←this, this1, eq]
    map_mul' := by simp only [map_mul, implies_true]
    map_add' := by simp only [map_add, implies_true]
    commutes' := by simp only [AlgHom.commutes, implies_true]






theorem IsSymAlg.liftCorrect {M M' : Type*} [AddCommMonoid M] [Module R M]
         {RM : Type*}
         [CommRing RM] [a : Algebra R RM] [CommRing M'] [Algebra R M']
         {iM : M →ₗ[R] RM} (salg : IsSymAlg iM) (phi : M →ₗ[R] M') :
         ((IsSymAlg.lift R salg phi) ∘ₗ iM) = phi := ((salg.ex_map phi).choose_spec.1).symm



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
      let e : M := B ⟨0, by aesop⟩
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
            have : idx ∈ Finset.univ := by
              simp only [Finset.mem_univ]
            exact False.elim (h this)
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
        simp only [AlgHom.toLinearMap_apply]
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
    ex_map_self := by
      intro φ
      have : Module.Finite R M := Module.finite_of_finrank_eq_succ r1
      let B := Module.finBasis R M
      -- Take e to be the unique element of our basis B

      let idx : Fin (Module.finrank R M) := Fin.mk 0 (by rw [r1]; exact Nat.zero_lt_one)
      let e : M := B ⟨0, by aesop⟩
      -- Use Polynomial.aeval to define a morphism φ' : Polynomial R →ₐ[R] A which
      -- takes X and maps it to φ(e)
      let φ' : Polynomial R →ₐ[R] Polynomial R := Polynomial.aeval (φ e)

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
            have : idx ∈ Finset.univ := by
              simp only [Finset.mem_univ]
            exact False.elim (h this)
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
        simp only [AlgHom.toLinearMap_apply]
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
         : RM₁ ⊗[R] RM₂ →ₐ[R] RM := by
  let φ₁ : M₁ →ₗ[R] RM := LinearMap.comp iM (LinearMap.prod LinearMap.id 0)
  let φ₂ : M₂ →ₗ[R] RM := LinearMap.comp iM (LinearMap.prod 0 LinearMap.id)

  let φ₁_alg : RM₁ →ₐ[R] RM := (salg₁.ex_map φ₁).exists.choose
  let φ₂_alg : RM₂ →ₐ[R] RM := (salg₂.ex_map φ₂).exists.choose

  let bilin_map : RM₁ →ₗ[R] RM₂ →ₗ[R] RM := by
    refine LinearMap.mk₂ R (fun x y => φ₁_alg x * φ₂_alg y) ?_ ?_ ?_ ?_
    · intros x y z
      simp only [map_add]
      exact RightDistribClass.right_distrib (φ₁_alg x) (φ₁_alg y) (φ₂_alg z)
    · intros r x y
      simp [Algebra.smul_def, mul_assoc]
    · intros x y z
      simp [add_mul]
      exact LeftDistribClass.left_distrib (φ₁_alg x) (φ₂_alg y) (φ₂_alg z)
    · intros r x y
      simp [Algebra.smul_def, mul_assoc]
      exact Algebra.left_comm (φ₁_alg x) r (φ₂_alg y)
  let lin_map : RM₁ ⊗[R] RM₂ →ₗ[R] RM := TensorProduct.lift bilin_map
  exact Algebra.TensorProduct.productMap φ₁_alg φ₂_alg




variable (I : Type*) (basis_I : Basis I R L)

def basisToPoly : L →ₗ[R] MvPolynomial I R :=
    Basis.constr basis_I R (fun i ↦ MvPolynomial.X i)

/-
This should be a more conceptual version of the proof below
-/
def cor1 : IsSymAlg (basisToPoly R L I basis_I) where
  ex_map := by
    intro alg b c φ
    simp[basisToPoly]

    use MvPolynomial.aeval (R := R) (fun i => φ (basis_I i))
    constructor
    · apply Basis.ext basis_I
      intro i
      simp

    · simp
      intro f hf
      apply MvPolynomial.algHom_ext
      intro i
      simp only [aeval_X]
      -- Should be very simple to prove this
      rw [hf]
      simp only [LinearMap.coe_comp, LieHom.coe_toLinearMap, AlgHom.coe_toLieHom,
        Function.comp_apply, Basis.constr_basis]
      simp only [AlgHom.toLinearMap_apply]
  ex_map_self := by
    intro φ
    simp[basisToPoly]

    use MvPolynomial.aeval (R := R) (fun i => φ (basis_I i))
    constructor
    · apply Basis.ext basis_I
      intro i
      simp

    · simp
      intro f hf
      apply MvPolynomial.algHom_ext
      intro i
      simp only [bind₁_X_right]
      -- Should be very simple to prove this
      rw [hf]
      simp only [LinearMap.coe_comp, LieHom.coe_toLinearMap, AlgHom.coe_toLieHom,
        Function.comp_apply, Basis.constr_basis]
      simp only [AlgHom.toLinearMap_apply]



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
  unfold mkAlgHom
  unfold GradedAlgebra.proj
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toLinearMap, LinearMap.coe_comp,
    Submodule.coe_subtype, Function.comp_apply, DFinsupp.lapply_apply]
  induction x using TensorAlgebra.induction
  case algebraMap r =>
    simp only [AlgHom.commutes]
    sorry
  case mul a b ha hb =>
    simp only [map_mul]
    sorry
  case add a b ha hb =>
    simp only [map_add, DFinsupp.coe_add, Pi.add_apply, Submodule.coe_add]
    exact Mathlib.Tactic.LinearCombination.add_eq_eq ha hb
  case _ x =>
    sorry
