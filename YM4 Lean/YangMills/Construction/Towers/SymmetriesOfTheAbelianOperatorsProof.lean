import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Towers.AlgebraOfTheLeftChart
import YangMills.Construction.Towers.LinearMapsOfTheWholeLatticeAreOntoProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.LogarithmsOfTheAbelianOperatorsProof
import YangMills.Construction.Towers.PlaquettesOfAnAbelianFieldProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianSymmetryProof
open Matrices AbelianFieldFacts UnitLatticeL2 AbelianFieldDensity
section Matrices
theorem cartanPhase_eq_diag (ϑ : ℝ) :
    cartanPhase ϑ = !![Complex.exp (Complex.I * ϑ), 0; 0, Complex.exp (-(Complex.I * ϑ))] := by apply _root_.YangMills.Construction.Tower.AbelianActionGradient.cartanPhase_eq_diagonal <;> assumption
theorem cartanPhase_inv_eq_diag (ϑ : ℝ) :
    (cartanPhase ϑ)⁻¹ = !![Complex.exp (-(Complex.I * ϑ)), 0; 0, Complex.exp (Complex.I * ϑ)] := by
  apply Matrix.inv_eq_right_inv
  rw [cartanPhase_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← Complex.exp_add]
theorem cartanPhase_mul_inv (ϑ : ℝ) : cartanPhase ϑ * (cartanPhase ϑ)⁻¹ = 1 := by
  rw [cartanPhase_inv_eq_diag, cartanPhase_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← Complex.exp_add]
theorem cartanPhase_inv_mul (ϑ : ℝ) : (cartanPhase ϑ)⁻¹ * cartanPhase ϑ = 1 := by
  rw [cartanPhase_inv_eq_diag, cartanPhase_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← Complex.exp_add]
theorem cartanPhase_inv (ϑ : ℝ) : (cartanPhase ϑ)⁻¹ = cartanPhase (-ϑ) := by apply _root_.YangMills.Construction.Tower.AbelianFieldPlaquettes.cartanPhase_inverse <;> assumption
theorem cartanPhase_zero : cartanPhase 0 = 1 := by apply _root_.YangMills.Construction.Tower.AbelianFieldPlaquettes.cartanPhase_at_zero <;> assumption
theorem conjugateBy_cartanPhase (t : ℝ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (cartanPhase t) X =
      !![X 0 0, Complex.exp (2 * Complex.I * t) * X 0 1;
        Complex.exp (-(2 * Complex.I * t)) * X 1 0, X 1 1] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.conjugateBy_cartanPhase <;> assumption
theorem cartanPhase_mem_specialUnitary (ϑ : ℝ) :
    cartanPhase ϑ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.Tower.AbelianFieldPlaquettes.cartanPhase_mem_compact <;> assumption
theorem mem_traceless_iff {X : ComplexMatrix2} :
    X ∈ ComplexMatrix2.traceless ↔ X 0 0 + X 1 1 = 0 := by
  show Matrix.trace X = 0 ↔ _
  rw [Matrix.trace_fin_two]
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
theorem traceless_ext_of_halfTrace {Z W : ComplexMatrix2} (hZ : Z ∈ ComplexMatrix2.traceless)
    (hW : W ∈ ComplexMatrix2.traceless)
    (h : ∀ a, ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily a * Z) =
      ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily a * W)) : Z = W := by apply _root_.YangMills.Construction.LieInnerProductProof.eq_of_halfTracePairing_pauli_eq <;> assumption
structure EntrywiseSymmetry (S : ComplexMatrix2 →+ ComplexMatrix2) (S' : ComplexMatrix2 →+ ComplexMatrix2)
    (φ : ℂ →+ ℂ) : Prop where
  maps_traceless : ∀ X ∈ ComplexMatrix2.traceless, S X ∈ ComplexMatrix2.traceless
  inv_maps_traceless : ∀ X ∈ ComplexMatrix2.traceless, S' X ∈ ComplexMatrix2.traceless
  right_inv : ∀ X, S (S' X) = X
  halfTrace_mul : ∀ X Y, ComplexMatrix2.halfTrace (S X * S Y) =
    φ (ComplexMatrix2.halfTrace (X * Y))
  comm_cartan : ∀ (t : ℝ) X, S (ComplexMatrix2.conjugateBy (cartanPhase t) X) =
    ComplexMatrix2.conjugateBy (cartanPhase t) (S X)
def cartanConj (ϑ : ℝ) : ComplexMatrix2 →+ ComplexMatrix2 where
  toFun := ComplexMatrix2.conjugateBy (cartanPhase ϑ)
  map_zero' := by simp [ComplexMatrix2.conjugateBy]
  map_add' := fun X Y => by simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
def conjTransposeHom : ComplexMatrix2 →+ ComplexMatrix2 where
  toFun := ComplexMatrix2.adjointMatrix
  map_zero' := by simp [ComplexMatrix2.adjointMatrix]
  map_add' := fun X Y => by simp [ComplexMatrix2.adjointMatrix]
def scalarHom (c : ℂ) : ComplexMatrix2 →+ ComplexMatrix2 where
  toFun := fun X => c • X
  map_zero' := by simp
  map_add' := fun X Y => by simp
theorem cartanConj_apply (ϑ : ℝ) (X : ComplexMatrix2) :
    cartanConj ϑ X = ComplexMatrix2.conjugateBy (cartanPhase ϑ) X := rfl
theorem conjugateBy_cartanPhase_smul (ϑ : ℝ) (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (cartanPhase ϑ) (c • X) =
      c • ComplexMatrix2.conjugateBy (cartanPhase ϑ) X := by
  simp [ComplexMatrix2.conjugateBy]
theorem cartanConj_entrywiseSymmetry (ϑ : ℝ) :
    EntrywiseSymmetry (cartanConj ϑ) (cartanConj (-ϑ)) (AddMonoidHom.id ℂ) where
  maps_traceless := fun X hX => by
    rw [mem_traceless_iff] at hX ⊢
    rw [cartanConj_apply, conjugateBy_cartanPhase]
    simpa using hX
  inv_maps_traceless := fun X hX => by
    rw [mem_traceless_iff] at hX ⊢
    rw [cartanConj_apply, conjugateBy_cartanPhase]
    simpa using hX
  right_inv := fun X => by
    have e₁ : cartanPhase (-ϑ) = (cartanPhase ϑ)⁻¹ := (cartanPhase_inv ϑ).symm
    have e₂ : (cartanPhase (-ϑ))⁻¹ = cartanPhase ϑ := by
      rw [cartanPhase_inv, neg_neg]
    show cartanPhase ϑ * (cartanPhase (-ϑ) * X * (cartanPhase (-ϑ))⁻¹) * (cartanPhase ϑ)⁻¹ = X
    rw [e₂, e₁]
    calc cartanPhase ϑ * ((cartanPhase ϑ)⁻¹ * X * cartanPhase ϑ) * (cartanPhase ϑ)⁻¹
        = (cartanPhase ϑ * (cartanPhase ϑ)⁻¹) * X * (cartanPhase ϑ * (cartanPhase ϑ)⁻¹) := by
          simp only [mul_assoc]
      _ = X := by rw [cartanPhase_mul_inv]; simp
  halfTrace_mul := fun X Y => by
    show ComplexMatrix2.halfTrace (cartanPhase ϑ * X * (cartanPhase ϑ)⁻¹ *
        (cartanPhase ϑ * Y * (cartanPhase ϑ)⁻¹)) =
      ComplexMatrix2.halfTrace (X * Y)
    have e : cartanPhase ϑ * X * (cartanPhase ϑ)⁻¹ * (cartanPhase ϑ * Y * (cartanPhase ϑ)⁻¹) =
        cartanPhase ϑ * (X * ((cartanPhase ϑ)⁻¹ * cartanPhase ϑ) * Y * (cartanPhase ϑ)⁻¹) := by
      simp only [mul_assoc]
    rw [e, cartanPhase_inv_mul, mul_one]
    show (1 / 2 : ℂ) * Matrix.trace (cartanPhase ϑ * (X * Y * (cartanPhase ϑ)⁻¹)) =
      (1 / 2 : ℂ) * Matrix.trace (X * Y)
    rw [Matrix.trace_mul_comm, mul_assoc (X * Y), cartanPhase_inv_mul, mul_one]
  comm_cartan := fun t X => by
    simp only [cartanConj_apply, conjugateBy_cartanPhase]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
theorem conjTransposeHom_entrywiseSymmetry :
    EntrywiseSymmetry conjTransposeHom conjTransposeHom (starRingEnd ℂ).toAddMonoidHom where
  maps_traceless := fun X hX => by
    rw [mem_traceless_iff] at hX ⊢
    show star (X 0 0) + star (X 1 1) = 0
    rw [← star_add, hX, star_zero]
  inv_maps_traceless := fun X hX => by
    rw [mem_traceless_iff] at hX ⊢
    show star (X 0 0) + star (X 1 1) = 0
    rw [← star_add, hX, star_zero]
  right_inv := fun X => Matrix.conjTranspose_conjTranspose X
  halfTrace_mul := fun X Y => by
    show (1 / 2 : ℂ) * Matrix.trace (X.conjTranspose * Y.conjTranspose) =
      conj ((1 / 2 : ℂ) * Matrix.trace (X * Y))
    rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, Matrix.trace_mul_comm, map_mul]
    simp [map_ofNat]
  comm_cartan := fun t X => by
    have hc : conj (Complex.exp (2 * Complex.I * t)) = Complex.exp (-(2 * Complex.I * t)) := by
      rw [← Complex.exp_conj]; simp [map_ofNat]
    have hc' : conj (Complex.exp (-(2 * Complex.I * t))) = Complex.exp (2 * Complex.I * t) := by
      rw [← Complex.exp_conj]; simp [map_ofNat]
    show (ComplexMatrix2.conjugateBy (cartanPhase t) X).conjTranspose =
      ComplexMatrix2.conjugateBy (cartanPhase t) X.conjTranspose
    simp only [conjugateBy_cartanPhase]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, hc, hc']
theorem scalarHom_entrywiseSymmetry {c : ℂ} (hc : c ≠ 0) :
    EntrywiseSymmetry (scalarHom c) (scalarHom c⁻¹) (AddMonoidHom.mulLeft (c * c)) where
  maps_traceless := fun X hX => ComplexMatrix2.traceless.smul_mem c hX
  inv_maps_traceless := fun X hX => ComplexMatrix2.traceless.smul_mem c⁻¹ hX
  right_inv := fun X => by
    show c • c⁻¹ • X = X
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  halfTrace_mul := fun X Y => by
    show (1 / 2 : ℂ) * Matrix.trace ((c • X) * (c • Y)) =
      c * c * ((1 / 2 : ℂ) * Matrix.trace (X * Y))
    rw [smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
    ring
  comm_cartan := fun t X => (conjugateBy_cartanPhase_smul t c X).symm
end Matrices
section Bonds
open InfiniteLattice
variable {a : ℝ}
theorem extendOddly_of_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem extendOddly_mem_complexEdgeForms (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (hf : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    FullSpace.extendOddly f ∈ FullSpace.complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendOddly_mem <;> assumption
theorem oddFunctions_ext {B B' : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : ∀ b : InfiniteLattice.Link a, B b.opposite = -B b)
    (hB' : ∀ b : InfiniteLattice.Link a, B' b.opposite = -B' b)
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → B b = B' b) : B = B' := by apply _root_.YangMills.Construction.Tower.FullSpace.Surjectivity.eq_of_eq_on_positive <;> assumption
theorem map_extendOddly (S : ComplexMatrix2 →+ ComplexMatrix2)
    (f : InfiniteLattice.Link a → ComplexMatrix2) :
    (fun b => S (FullSpace.extendOddly f b)) = FullSpace.extendOddly fun b => S (f b) := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_of_positive f hb, extendOddly_of_positive _ hb]
  · have e : FullSpace.extendOddly f b = -f b.opposite := if_neg hb
    have e' : FullSpace.extendOddly (fun b => S (f b)) b = -S (f b.opposite) := if_neg hb
    rw [e, e', map_neg]
theorem map_mem_complexEdgeForms {S S' : ComplexMatrix2 →+ ComplexMatrix2} {φ : ℂ →+ ℂ}
    (hS : EntrywiseSymmetry S S' φ)
    {B : InfiniteLattice.Link a → ComplexMatrix2} (hB : B ∈ FullSpace.complexEdgeForms a) :
    (fun b => S (B b)) ∈ FullSpace.complexEdgeForms a :=
  ⟨fun b hb => hS.maps_traceless _ (hB.1 b hb), fun b => by
    show S (B b.opposite) = -S (B b)
    rw [hB.2 b, map_neg]⟩
end Bonds
section Pairings
variable {ι : Type}
theorem traceFinsumPairing_map {S S' : ComplexMatrix2 →+ ComplexMatrix2} {φ : ℂ →+ ℂ}
    (hS : EntrywiseSymmetry S S' φ) (f h : ι → ComplexMatrix2)
    (hh : (Function.support fun i => ComplexMatrix2.halfTrace (f i * h i)).Finite) :
    traceFinsumPairing (fun i => S (f i)) (fun i => S (h i)) = φ (traceFinsumPairing f h) := by
  unfold traceFinsumPairing
  rw [AddMonoidHom.map_finsum φ hh]
  exact finsum_congr fun i => hS.halfTrace_mul _ _
theorem halfTrace_support_finite_right (f h : ι → ComplexMatrix2) (hh : HasFiniteSupp h) :
    (Function.support fun i => ComplexMatrix2.halfTrace (f i * h i)).Finite := by
  refine Set.Finite.subset hh fun i hi hz => hi ?_
  show ComplexMatrix2.halfTrace (f i * h i) = 0
  rw [hz]
  simp
theorem halfTrace_support_finite_left (f h : ι → ComplexMatrix2) (hf : HasFiniteSupp f) :
    (Function.support fun i => ComplexMatrix2.halfTrace (f i * h i)).Finite := by
  refine Set.Finite.subset hf fun i hi hz => hi ?_
  show ComplexMatrix2.halfTrace (f i * h i) = 0
  rw [hz]
  simp
theorem traceFinsumPairing_single [DecidableEq ι] (Z : ι → ComplexMatrix2) (x : ι)
    (Y : ComplexMatrix2) :
    traceFinsumPairing Z (Pi.single x Y) = ComplexMatrix2.halfTrace (Z x * Y) := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.traceFinsumPairing_single <;> assumption
theorem traceless_funext [DecidableEq ι] {Z W : ι → ComplexMatrix2}
    (hZ : ∀ x, Z x ∈ ComplexMatrix2.traceless) (hW : ∀ x, W x ∈ ComplexMatrix2.traceless)
    (h : ∀ x, ∀ Y ∈ ComplexMatrix2.traceless,
      traceFinsumPairing Z (Pi.single x Y) = traceFinsumPairing W (Pi.single x Y)) : Z = W := by
  funext x
  refine traceless_ext_of_halfTrace (hZ x) (hW x) fun a => ?_
  have e := h x _ (pauliFamily_mem_traceless a)
  rw [traceFinsumPairing_single, traceFinsumPairing_single] at e
  show (1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.pauliFamily a * Z x) =
    (1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.pauliFamily a * W x)
  rw [Matrix.trace_mul_comm, Matrix.trace_mul_comm (ComplexMatrix2.pauliFamily a)]
  exact e
theorem hasFiniteSupp_single [DecidableEq ι] (x : ι) (Y : ComplexMatrix2) :
    HasFiniteSupp (Pi.single x Y : ι → ComplexMatrix2) := by
  refine Set.Finite.subset (Set.finite_singleton x) fun i hi => ?_
  by_contra hne
  exact hi (Pi.single_eq_of_ne hne _)
end Pairings
section Difference
open UnitGaugeDirections
variable {L : ℕ} {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
def IsCartanValued (U : FullSpace.Edge L 0 0 → ComplexMatrix2) : Prop :=
  ∀ b, ∃ t : ℝ, U b = cartanPhase t
theorem abelianLinkField_isCartanValued (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    IsCartanValued (FullSpace.abelianLinkField θ) := by
  intro b
  unfold FullSpace.abelianLinkField
  split_ifs with h h'
  · exact ⟨θ ⟨b, h⟩, rfl⟩
  · exact ⟨-θ ⟨b.opposite, h'⟩, by rw [← cartanPhase_inv]; rfl⟩
  · exact ⟨0, cartanPhase_zero.symm⟩
variable {S S' : ComplexMatrix2 →+ ComplexMatrix2} {φ : ℂ →+ ℂ}
theorem covDiff_map (hS : EntrywiseSymmetry S S' φ) (hU : IsCartanValued U)
    (l : FullSpace.Vertex L 0 0 → ComplexMatrix2) :
    FullSpace.covDiff U (fun x => S (l x)) =
      fun b => S (FullSpace.covDiff U l b) := by
  unfold FullSpace.covDiff
  rw [map_extendOddly]
  congr 1
  funext b
  obtain ⟨t, ht⟩ := hU b
  rw [ht, map_sub, hS.comm_cartan]
theorem map_mem_vertexComplex (hS : EntrywiseSymmetry S S' φ)
    {l : FullSpace.Vertex L 0 0 → ComplexMatrix2}
    (hl : l ∈ (unitVertexSpace L).complexSubmodule) :
    (fun x => S (l x)) ∈ (unitVertexSpace L).complexSubmodule :=
  fun x _ => hS.maps_traceless _ (hl x (Set.mem_univ x))
theorem covDiffAdjoint_pairing (hD : CovDiffAndAdjoint U)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ (unitEdgeSpace L).complexSubmodule)
    {l : FullSpace.Vertex L 0 0 → ComplexMatrix2} (hl : l ∈ (unitVertexSpace L).complexSubmodule)
    (hf : HasFiniteSupp l) :
    traceFinsumPairing (FullSpace.covDiffAdjoint U B) l =
        FullSpace.finiteEdgePairing B (FullSpace.covDiff U l) ∧
      HasFiniteSupp (FullSpace.restrictToPositiveEdges (FullSpace.covDiff U l)) := by
  obtain ⟨_, hmap, hcarry, htr, hval⟩ := hD
  have e := htr ⟨B, hB⟩ ⟨l, hl⟩ hf
  have c := hcarry ⟨l, hl⟩ hf
  rw [hmap ⟨l, hl⟩] at e c
  refine ⟨?_, c⟩
  rw [hval ⟨B, hB⟩]
  exact e
theorem covDiffAdjoint_map (hS : EntrywiseSymmetry S S' φ) (hU : IsCartanValued U)
    (hD : CovDiffAndAdjoint U) (hF : CompositesDefined U)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ (unitEdgeSpace L).complexSubmodule) :
    FullSpace.covDiffAdjoint U (fun b => S (B b)) =
      fun x => S (FullSpace.covDiffAdjoint U B x) := by
  classical
  have hB' : (fun b => S (B b)) ∈ (unitEdgeSpace L).complexSubmodule :=
    map_mem_complexEdgeForms hS hB
  have hT := (hF.2 B hB).1
  have hT' := (hF.2 _ hB').1
  refine traceless_funext (fun x => hT' x (Set.mem_univ x))
    (fun x => hS.maps_traceless _ (hT x (Set.mem_univ x))) fun x Y hY => ?_
  have hf : (Pi.single x (S' Y) : FullSpace.Vertex L 0 0 → ComplexMatrix2) ∈
      (unitVertexSpace L).complexSubmodule := by
    intro i _
    by_cases hi : i = x
    · subst hi
      simpa using hS.inv_maps_traceless _ hY
    · rw [Pi.single_eq_of_ne hi]
      exact ComplexMatrix2.traceless.zero_mem
  have hs : (fun i => S ((Pi.single x (S' Y) : FullSpace.Vertex L 0 0 → ComplexMatrix2) i)) =
      Pi.single x Y := by
    funext i
    by_cases hi : i = x
    · subst hi
      simpa using hS.right_inv Y
    · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, map_zero]
  have hfin : HasFiniteSupp (Pi.single x (S' Y) : FullSpace.Vertex L 0 0 → ComplexMatrix2) :=
    hasFiniteSupp_single x _
  have r₀ := covDiffAdjoint_pairing hD hB hf hfin
  have r₁ := covDiffAdjoint_pairing hD hB' (map_mem_vertexComplex hS hf)
    (by rw [hs]; exact hasFiniteSupp_single x _)
  rw [← hs, r₁.1, covDiff_map hS hU,
    traceFinsumPairing_map hS _ _ (halfTrace_support_finite_right _ _ hfin)]
  show traceFinsumPairing (fun b => S (FullSpace.restrictToPositiveEdges B b))
    (fun b => S (FullSpace.restrictToPositiveEdges (FullSpace.covDiff U _) b)) = _
  rw [traceFinsumPairing_map hS _ _ (halfTrace_support_finite_right _ _ r₀.2)]
  exact congrArg φ r₀.1.symm
theorem gaugeLaplacian_map (hS : EntrywiseSymmetry S S' φ) (hU : IsCartanValued U)
    (hD : CovDiffAndAdjoint U) (hF : CompositesDefined U)
    {l : FullSpace.Vertex L 0 0 → ComplexMatrix2} (hl : l ∈ (unitVertexSpace L).complexSubmodule) :
    FullSpace.gaugeLaplacian U (fun x => S (l x)) =
      fun x => S (FullSpace.gaugeLaplacian U l x) := by
  unfold FullSpace.gaugeLaplacian
  rw [covDiff_map hS hU, covDiffAdjoint_map hS hU hD hF (hF.1 l hl).1]
theorem massiveHessian_map (hS : EntrywiseSymmetry S S' φ) (hU : IsCartanValued U)
    (hD : CovDiffAndAdjoint U) (hF : CompositesDefined U)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2} (hB : B ∈ (unitEdgeSpace L).complexSubmodule)
    (hA : FullSpace.complexHessianOperator U (fun b => S (B b)) =
      fun b => S (FullSpace.complexHessianOperator U B b)) :
    FullSpace.massiveHessian U (fun b => S (B b)) =
      fun b => S (FullSpace.massiveHessian U B b) := by
  unfold FullSpace.massiveHessian
  rw [hA, covDiffAdjoint_map hS hU hD hF hB, covDiff_map hS hU]
  funext b
  simp
end Difference
section Coefficients
theorem pauliCombination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_pauliCombination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCombination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
def ActsOnPauliCoeffs (S : ComplexMatrix2 →+ ComplexMatrix2) (ψ : ℂ → ℂ) : Prop :=
  ∀ x : Fin 3 → ℂ, S (∑ a, x a • ComplexMatrix2.pauliFamily a) =
    ∑ a, ψ (x a) • ComplexMatrix2.pauliFamily a
theorem pauliCoeff_map {S : ComplexMatrix2 →+ ComplexMatrix2} {ψ : ℂ → ℂ}
    (h : ActsOnPauliCoeffs S ψ) (a : Fin 3)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (S X) = ψ (pauliCoeff a X) := by
  conv_lhs => rw [← pauliCombination_pauliCoeff hX, h]
  exact pauliCoeff_pauliCombination (fun b => ψ (pauliCoeff b X)) a
theorem scalarHom_actsOnPauliCoeffs (c : ℂ) :
    ActsOnPauliCoeffs (scalarHom c) (fun z => c * z) := fun x => by
  show c • ∑ a, x a • ComplexMatrix2.pauliFamily a = _
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
theorem conjTransposeHom_actsOnPauliCoeffs :
    ActsOnPauliCoeffs conjTransposeHom (starRingEnd ℂ) := fun x => by
  show (∑ a, x a • ComplexMatrix2.pauliFamily a).conjTranspose = _
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_smul, ← (pauliFamily_mem_hermitianTraceless a).1]
  rfl
end Coefficients
section Operator
open PeriodicOperators (applyKernel)
variable {L : ℕ} {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
theorem meshAt_pos (L : ℕ) (hL : 0 < L) : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.meshAt_zero_pos <;> assumption
theorem complexHessianOperator_of_positive (B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    {b : FullSpace.Edge L 0 0} (hb : b.IsPositivelyOriented) :
    FullSpace.complexHessianOperator U B b =
      ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel U)
        (toPauliCoeffs (FullSpace.restrictToPositiveEdges B))) ⟨b, hb⟩ := by
  unfold FullSpace.complexHessianOperator
  rw [extendOddly_of_positive _ hb]
  exact dif_pos hb
theorem complexHessianOperator_opposite (hL : 0 < L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (b : FullSpace.Edge L 0 0) :
    FullSpace.complexHessianOperator U B b.opposite = -FullSpace.complexHessianOperator U B b :=
  extendOddly_opposite (meshAt_pos L hL) _ b
theorem complexHessianOperator_mem (hL : 0 < L) (B : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.complexHessianOperator U B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by
  refine extendOddly_mem_complexEdgeForms (meshAt_pos L hL) _ fun b hb => ?_
  rw [dif_pos hb]
  exact pauliCombination_mem_traceless _
theorem complexHessianOperator_comm_of_pauliCoeffs (hL : 0 < L)
    {S : ComplexMatrix2 →+ ComplexMatrix2} {ψ : ℂ → ℂ}
    (hS : ActsOnPauliCoeffs S ψ)
    (hK : ∀ (f : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ) ι,
      applyKernel (FullSpace.complexHessianKernel U) (fun κ => ψ (f κ)) ι =
        ψ (applyKernel (FullSpace.complexHessianKernel U) f ι))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    FullSpace.complexHessianOperator U (fun b => S (B b)) =
      fun b => S (FullSpace.complexHessianOperator U B b) := by
  refine oddFunctions_ext (complexHessianOperator_opposite hL _) (fun b => ?_) fun b hb => ?_
  · show S _ = -S _
    rw [complexHessianOperator_opposite hL, map_neg]
  · rw [complexHessianOperator_of_positive _ hb, complexHessianOperator_of_positive _ hb]
    have e : toPauliCoeffs (FullSpace.restrictToPositiveEdges fun b => S (B b)) =
        fun κ => ψ (toPauliCoeffs (FullSpace.restrictToPositiveEdges B) κ) :=
      funext fun κ => pauliCoeff_map hS κ.1 (hB.1 _ κ.2.2)
    rw [e]
    show ∑ a, _ • ComplexMatrix2.pauliFamily a = S (∑ a, _ • ComplexMatrix2.pauliFamily a)
    rw [hS]
    exact Finset.sum_congr rfl fun a _ => by rw [hK]
theorem complexHessianOperator_comm_scalar (hL : 0 < L) (c : ℂ)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    FullSpace.complexHessianOperator U (fun b => scalarHom c (B b)) =
      fun b => scalarHom c (FullSpace.complexHessianOperator U B b) := by
  refine complexHessianOperator_comm_of_pauliCoeffs hL (scalarHom_actsOnPauliCoeffs c)
    (fun f ι => ?_) hB
  show ∑' κ, _ * (c * f κ) = c * ∑' κ, _ * f κ
  rw [← tsum_mul_left]
  exact tsum_congr fun κ => mul_left_comm _ _ _
theorem complexHessianOperator_comm_conjTranspose (hL : 0 < L)
    (hK : ∀ ι' ι, (FullSpace.complexHessianKernel U ι' ι).im = 0)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    FullSpace.complexHessianOperator U (fun b => conjTransposeHom (B b)) =
      fun b => conjTransposeHom (FullSpace.complexHessianOperator U B b) := by
  refine complexHessianOperator_comm_of_pauliCoeffs hL conjTransposeHom_actsOnPauliCoeffs
    (fun f ι => ?_) hB
  show ∑' κ, _ * conj (f κ) = conj (∑' κ, _ * f κ)
  rw [Complex.conj_tsum]
  refine tsum_congr fun κ => ?_
  rw [map_mul, Complex.conj_eq_iff_im.mpr (hK _ _)]
end Operator
section Gauge
open PeriodicOperators (applyKernel)
open HessianKernel (finiteSupportComplexForms)
variable {L : ℕ} {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
theorem adjointForm_const_cartan (hL : 0 < L) (ϑ : ℝ) {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    FullSpace.adjointForm (fun _ => cartanPhase ϑ) B = fun b => cartanConj ϑ (B b) := by
  refine oddFunctions_ext (extendOddly_opposite (meshAt_pos L hL) _) (fun b => ?_)
    fun b hb => ?_
  · show cartanConj ϑ _ = -cartanConj ϑ _
    rw [hB.2 b, map_neg]
  · exact extendOddly_of_positive _ hb
theorem gaugeAct_const_cartan (hU : IsCartanValued U) (ϑ : ℝ) :
    FullSpace.gaugeAct (fun _ => cartanPhase ϑ) U = U := by
  funext b
  obtain ⟨t, ht⟩ := hU b
  show ComplexMatrix2.conjugateBy (cartanPhase ϑ) (U b) = U b
  rw [ht, conjugateBy_cartanPhase, cartanPhase_eq_diag t]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem restrictToPositiveEdges_hasFiniteSupp {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (h : FullSpace.HasFiniteEdgeSupport B) :
    HasFiniteSupp (FullSpace.restrictToPositiveEdges B) :=
  (Set.Finite.preimage Subtype.val_injective.injOn h).subset fun b hb => ⟨b.2, hb⟩
theorem map_hasFiniteEdgeSupport (S : ComplexMatrix2 →+ ComplexMatrix2)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (h : FullSpace.HasFiniteEdgeSupport B) : FullSpace.HasFiniteEdgeSupport fun b => S (B b) :=
  Set.Finite.subset h fun b hb => ⟨hb.1, fun hz => hb.2 (by
    show S (B b) = 0
    rw [hz, map_zero])⟩
theorem basisForm_of_positive (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0))
    {c : FullSpace.Edge L 0 0} (hc : c.IsPositivelyOriented) :
    FullSpace.basisForm a b c =
      open Classical in if c = b.1 then ComplexMatrix2.pauliFamily a else 0 :=
  extendOddly_of_positive _ hc
theorem basisForm_mem_edgeFormSpace (hL : 0 < L) (a : Fin 3)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.basisForm a b ∈ FullSpace.edgeFormSpace (meshAt L 0 0) := by
  refine ⟨fun c hc => ?_, extendOddly_opposite (meshAt_pos L hL) _⟩
  rw [basisForm_of_positive a b hc]
  split_ifs
  · exact pauliFamily_mem_hermitianTraceless a
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
theorem basisForm_mem_complexEdgeForms (hL : 0 < L) (a : Fin 3)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.basisForm a b ∈ FullSpace.complexEdgeForms (meshAt L 0 0) :=
  ⟨fun c hc => ((basisForm_mem_edgeFormSpace hL a b).1 c hc).2,
    (basisForm_mem_edgeFormSpace hL a b).2⟩
theorem basisForm_hasFiniteEdgeSupport (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.HasFiniteEdgeSupport (FullSpace.basisForm a b) := by apply _root_.YangMills.SharedProofs.p37344 <;> assumption
theorem edgeFormPairing_basisForm (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0))
    (X : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.finiteEdgePairing (FullSpace.basisForm a b) X =
      ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily a * X b.1) := by
  unfold FullSpace.finiteEdgePairing traceFinsumPairing
  rw [finsum_eq_single _ b]
  · show ComplexMatrix2.halfTrace (FullSpace.basisForm a b b.1 * X b.1) = _
    rw [basisForm_of_positive a b b.2, if_pos rfl]
  · intro c hc
    show ComplexMatrix2.halfTrace (FullSpace.basisForm a b c.1 * X c.1) = 0
    rw [basisForm_of_positive a b c.2, if_neg fun h => hc (Subtype.ext h)]
    simp
theorem complexHessianOperator_comm_cartan_of_finite (hL : 0 < L) (hU : IsCartanValued U)
    (hUc : U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (hG : FullSpace.LeftChartAlgebra.DerivativeIdentities L 0 0)
    (hP : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U B') =
        FullSpace.complexActionHessian U B B')
    (ϑ : ℝ) {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) (hf : FullSpace.HasFiniteEdgeSupport B) :
    FullSpace.complexHessianOperator U (fun b => cartanConj ϑ (B b)) =
      fun b => cartanConj ϑ (FullSpace.complexHessianOperator U B b) := by
  have hS := cartanConj_entrywiseSymmetry ϑ
  have hS' := cartanConj_entrywiseSymmetry (-ϑ)
  refine oddFunctions_ext (complexHessianOperator_opposite hL _) (fun b => ?_) fun b hb => ?_
  · show cartanConj ϑ _ = -cartanConj ϑ _
    rw [complexHessianOperator_opposite hL, map_neg]
  refine traceless_ext_of_halfTrace ((complexHessianOperator_mem hL _).1 b hb)
    (hS.maps_traceless _ ((complexHessianOperator_mem hL _).1 b hb)) fun a => ?_
  have hEc := basisForm_mem_complexEdgeForms hL a
    (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
  have hEf := basisForm_hasFiniteEdgeSupport (L := L) a
    (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
  obtain ⟨E, hE⟩ : ∃ E, E = FullSpace.basisForm a
    (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0)) := ⟨_, rfl⟩
  rw [← hE] at hEc hEf
  have hE₀c : (fun c => cartanConj (-ϑ) (E c)) ∈ FullSpace.complexEdgeForms (meshAt L 0 0) :=
    map_mem_complexEdgeForms hS' hEc
  have hE₀f : FullSpace.HasFiniteEdgeSupport fun c => cartanConj (-ϑ) (E c) :=
    map_hasFiniteEdgeSupport _ hEf
  have hEE : (fun c => cartanConj ϑ (cartanConj (-ϑ) (E c))) = E :=
    funext fun c => hS.right_inv _
  have l₁ := hP E ⟨hEc, hEf⟩ (fun b => cartanConj ϑ (B b))
    ⟨map_mem_complexEdgeForms hS hB, map_hasFiniteEdgeSupport _ hf⟩
  have g := (hG U (fun _ => cartanPhase ϑ) 0 (fun c => cartanConj (-ϑ) (E c)) B hUc
    (fun _ => (Matrix.mem_specialUnitaryGroup_iff.mp (cartanPhase_mem_specialUnitary ϑ)).2)
    (fun _ => ComplexMatrix2.traceless.zero_mem) (by simp [HasFiniteSupp]) hE₀c hB hE₀f hf).2.1
  rw [gaugeAct_const_cartan hU, adjointForm_const_cartan hL ϑ hE₀c,
    adjointForm_const_cartan hL ϑ hB, hEE] at g
  have l₂ := hP _ ⟨hE₀c, hE₀f⟩ B ⟨hB, hf⟩
  have l₃ : FullSpace.finiteEdgePairing E
      (fun c => cartanConj ϑ (FullSpace.complexHessianOperator U B c)) =
      FullSpace.finiteEdgePairing (fun c => cartanConj (-ϑ) (E c))
        (FullSpace.complexHessianOperator U B) := by
    conv_lhs => rw [← hEE]
    exact traceFinsumPairing_map hS _ _
      (halfTrace_support_finite_left _ _ (restrictToPositiveEdges_hasFiniteSupp hE₀f))
  have t₁ := edgeFormPairing_basisForm a (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
    (FullSpace.complexHessianOperator U fun b => cartanConj ϑ (B b))
  have t₂ := edgeFormPairing_basisForm a (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
    (fun c => cartanConj ϑ (FullSpace.complexHessianOperator U B c))
  rw [← hE] at t₁ t₂
  exact t₁.symm.trans (l₁.trans (g.trans (l₂.symm.trans (l₃.symm.trans t₂))))
def restrictToEdges (F : Set (FullSpace.PositiveEdge (meshAt L 0 0)))
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) : FullSpace.Edge L 0 0 → ComplexMatrix2 :=
  open Classical in FullSpace.extendOddly fun c => if c ∈ Subtype.val '' F then B c else 0
theorem restrictToEdges_of_mem {F : Set (FullSpace.PositiveEdge (meshAt L 0 0))}
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) {c : FullSpace.PositiveEdge (meshAt L 0 0)}
    (hc : c ∈ F) : restrictToEdges F B c.1 = B c.1 := by
  unfold restrictToEdges
  rw [extendOddly_of_positive _ c.2, if_pos ⟨c, hc, rfl⟩]
theorem restrictToEdges_mem (hL : 0 < L) (F : Set (FullSpace.PositiveEdge (meshAt L 0 0)))
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    restrictToEdges F B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by
  refine extendOddly_mem_complexEdgeForms (meshAt_pos L hL) _ fun c hc => ?_
  split_ifs
  · exact hB.1 c hc
  · exact ComplexMatrix2.traceless.zero_mem
theorem restrictToEdges_hasFiniteEdgeSupport {F : Set (FullSpace.PositiveEdge (meshAt L 0 0))}
    (hF : F.Finite) (B : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.HasFiniteEdgeSupport (restrictToEdges F B) := by
  refine (hF.image Subtype.val).subset fun c hc => ?_
  by_contra hne
  refine hc.2 ?_
  unfold restrictToEdges
  rw [extendOddly_of_positive _ hc.1, if_neg hne]
theorem restrictToEdges_map (S : ComplexMatrix2 →+ ComplexMatrix2)
    (F : Set (FullSpace.PositiveEdge (meshAt L 0 0))) (B : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    restrictToEdges F (fun b => S (B b)) = fun b => S (restrictToEdges F B b) := by
  unfold restrictToEdges
  rw [map_extendOddly]
  congr 1
  funext c
  split_ifs
  · rfl
  · rw [map_zero]
theorem complexHessianOperator_congr_of_row {F : Set (FullSpace.PositiveEdge (meshAt L 0 0))}
    {b : FullSpace.Edge L 0 0} (hb : b.IsPositivelyOriented)
    (hrow : ∀ (a : Fin 3) κ, FullSpace.complexHessianKernel U (a, ⟨b, hb⟩) κ ≠ 0 → κ.2 ∈ F)
    {B B' : FullSpace.Edge L 0 0 → ComplexMatrix2} (h : ∀ c ∈ F, B c.1 = B' c.1) :
    FullSpace.complexHessianOperator U B b = FullSpace.complexHessianOperator U B' b := by
  rw [complexHessianOperator_of_positive _ hb, complexHessianOperator_of_positive _ hb]
  show ∑ a, _ • ComplexMatrix2.pauliFamily a = ∑ a, _ • ComplexMatrix2.pauliFamily a
  refine Finset.sum_congr rfl fun a _ => congrArg (· • ComplexMatrix2.pauliFamily a) ?_
  show ∑' κ, _ * _ = ∑' κ, _ * _
  refine tsum_congr fun κ => ?_
  by_cases hk : FullSpace.complexHessianKernel U (a, ⟨b, hb⟩) κ = 0
  · simp [hk]
  · congr 1
    show pauliCoeff κ.1 (B κ.2.1) = pauliCoeff κ.1 (B' κ.2.1)
    rw [h _ (hrow a κ hk)]
theorem complexHessianOperator_comm_cartan (hL : 0 < L) (hU : IsCartanValued U)
    (hUc : U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (hG : FullSpace.LeftChartAlgebra.DerivativeIdentities L 0 0)
    (hP : ∀ B ∈ finiteSupportComplexForms L 0 0, ∀ B' ∈ finiteSupportComplexForms L 0 0,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U B') =
        FullSpace.complexActionHessian U B B')
    (hR : HessianKernel.RowFinite (FullSpace.complexHessianKernel U))
    (ϑ : ℝ) {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0)) :
    FullSpace.complexHessianOperator U (fun b => cartanConj ϑ (B b)) =
      fun b => cartanConj ϑ (FullSpace.complexHessianOperator U B b) := by
  refine oddFunctions_ext (complexHessianOperator_opposite hL _) (fun b => ?_) fun b hb => ?_
  · show cartanConj ϑ _ = -cartanConj ϑ _
    rw [complexHessianOperator_opposite hL, map_neg]
  obtain ⟨F, hF⟩ : ∃ F : Set (FullSpace.PositiveEdge (meshAt L 0 0)), F =
      ⋃ a : Fin 3, Prod.snd '' {κ | FullSpace.complexHessianKernel U (a, ⟨b, hb⟩) κ ≠ 0} :=
    ⟨_, rfl⟩
  have hFfin : F.Finite := by
    rw [hF]
    exact Set.finite_iUnion fun a => (hR _).image _
  have hrow : ∀ (a : Fin 3) κ, FullSpace.complexHessianKernel U (a, ⟨b, hb⟩) κ ≠ 0 → κ.2 ∈ F := by
    intro a κ hk
    rw [hF]
    exact Set.mem_iUnion.mpr ⟨a, κ, hk, rfl⟩
  have e₁ : FullSpace.complexHessianOperator U (fun b => cartanConj ϑ (B b)) b =
      FullSpace.complexHessianOperator U (restrictToEdges F fun b => cartanConj ϑ (B b)) b :=
    complexHessianOperator_congr_of_row hb hrow fun c hc =>
      (restrictToEdges_of_mem (fun b => cartanConj ϑ (B b)) hc).symm
  have e₂ : FullSpace.complexHessianOperator U B b =
      FullSpace.complexHessianOperator U (restrictToEdges F B) b :=
    complexHessianOperator_congr_of_row hb hrow fun c hc => (restrictToEdges_of_mem B hc).symm
  show _ = cartanConj ϑ _
  rw [e₁, e₂, restrictToEdges_map,
    complexHessianOperator_comm_cartan_of_finite hL hU hUc hG hP ϑ (restrictToEdges_mem hL F hB)
      (restrictToEdges_hasFiniteEdgeSupport hFfin B)]
end Gauge
section Sectors
open UnitGaugeDirections
theorem exp_two_I_quarter_pi :
    Complex.exp (2 * Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) = Complex.I := by
  have e : 2 * Complex.I * ((Real.pi / 4 : ℝ) : ℂ) = ((Real.pi : ℂ) / 2) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp
theorem exp_neg_two_I_quarter_pi :
    Complex.exp (-(2 * Complex.I * ((Real.pi / 4 : ℝ) : ℂ))) = -Complex.I := by
  rw [Complex.exp_neg, exp_two_I_quarter_pi, Complex.inv_I]
theorem cartanConj_quarter_pi (X : ComplexMatrix2) :
    cartanConj (Real.pi / 4) X = !![X 0 0, Complex.I * X 0 1; -Complex.I * X 1 0, X 1 1] := by
  rw [cartanConj_apply, conjugateBy_cartanPhase, exp_two_I_quarter_pi, exp_neg_two_I_quarter_pi]
theorem raisingPauli_eq : raisingPauli = !![0, 1; 0, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.raisingPauli_eq_matrix <;> assumption
theorem loweringPauli_eq : loweringPauli = !![0, 0; 1, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.loweringPauli_eq_matrix <;> assumption
theorem pauliFamily_two_eq : ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] := rfl
theorem eq_zero_of_mul_eq_mul_of_ne {a b y : ℂ} (hab : a ≠ b) (h : a * y = b * y) : y = 0 :=
  (mul_eq_zero.mp (show (a - b) * y = 0 by linear_combination h)).resolve_left
    (sub_ne_zero.mpr hab)
theorem imag_unit_ne_neg : Complex.I ≠ -Complex.I := by
  intro h
  have e : (2 : ℂ) * Complex.I = 0 := by linear_combination h
  simp at e
theorem imag_unit_ne_one : Complex.I ≠ 1 := by
  intro h
  have e := congrArg Complex.im h
  simp at e
theorem neg_imag_unit_ne_one : -Complex.I ≠ 1 := by
  intro h
  have e := congrArg Complex.im h
  simp at e
structure ChargeSector (t : ComplexMatrix2) (l : ℂ) : Prop where
  isEigen : cartanConj (Real.pi / 4) t = l • t
  eigenvalue_ne_zero : l ≠ 0
  eq_smul_of_eigen : ∀ Y ∈ ComplexMatrix2.traceless,
    cartanConj (Real.pi / 4) Y = l • Y → ∃ c : ℂ, Y = c • t
theorem chargeSector_neutral : ChargeSector (ComplexMatrix2.pauliFamily 2) 1 where
  isEigen := by
    rw [cartanConj_quarter_pi, pauliFamily_two_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  eigenvalue_ne_zero := one_ne_zero
  eq_smul_of_eigen := fun Y hY h => by
    rw [mem_traceless_iff] at hY
    rw [cartanConj_quarter_pi, one_smul] at h
    have h01 : Complex.I * Y 0 1 = 1 * Y 0 1 := by
      simpa using congrFun (congrFun h 0) 1
    have h10 : -Complex.I * Y 1 0 = 1 * Y 1 0 := by
      simpa using congrFun (congrFun h 1) 0
    have z01 := eq_zero_of_mul_eq_mul_of_ne imag_unit_ne_one h01
    have z10 := eq_zero_of_mul_eq_mul_of_ne neg_imag_unit_ne_one h10
    refine ⟨Y 0 0, ?_⟩
    rw [pauliFamily_two_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z01, z10]
    linear_combination hY
theorem chargeSector_raising : ChargeSector raisingPauli Complex.I where
  isEigen := by
    rw [cartanConj_quarter_pi, raisingPauli_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  eigenvalue_ne_zero := Complex.I_ne_zero
  eq_smul_of_eigen := fun Y hY h => by
    rw [mem_traceless_iff] at hY
    rw [cartanConj_quarter_pi] at h
    have h00 : Complex.I * Y 0 0 = 1 * Y 0 0 := by
      simpa using (congrFun (congrFun h 0) 0).symm
    have h10 : -Complex.I * Y 1 0 = Complex.I * Y 1 0 := by
      simpa using congrFun (congrFun h 1) 0
    have z00 := eq_zero_of_mul_eq_mul_of_ne imag_unit_ne_one h00
    have z10 := eq_zero_of_mul_eq_mul_of_ne imag_unit_ne_neg.symm h10
    refine ⟨Y 0 1, ?_⟩
    rw [raisingPauli_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z00, z10]
    linear_combination hY - z00
theorem chargeSector_lowering : ChargeSector loweringPauli (-Complex.I) where
  isEigen := by
    rw [cartanConj_quarter_pi, loweringPauli_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  eigenvalue_ne_zero := neg_ne_zero.mpr Complex.I_ne_zero
  eq_smul_of_eigen := fun Y hY h => by
    rw [mem_traceless_iff] at hY
    rw [cartanConj_quarter_pi] at h
    have h00 : -Complex.I * Y 0 0 = 1 * Y 0 0 := by
      simpa using (congrFun (congrFun h 0) 0).symm
    have h01 : Complex.I * Y 0 1 = -Complex.I * Y 0 1 := by
      simpa using congrFun (congrFun h 0) 1
    have z00 := eq_zero_of_mul_eq_mul_of_ne neg_imag_unit_ne_one h00
    have z01 := eq_zero_of_mul_eq_mul_of_ne imag_unit_ne_neg h01
    refine ⟨Y 1 0, ?_⟩
    rw [loweringPauli_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z00, z01]
    linear_combination hY - z00
variable {L : ℕ} {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
theorem gaugeLaplacian_preserves_sector {t : ComplexMatrix2} {c : ℂ} (hs : ChargeSector t c)
    (hU : IsCartanValued U) (hD : CovDiffAndAdjoint U) (hF : CompositesDefined U)
    {l : FullSpace.Vertex L 0 0 → ComplexMatrix2} (hl : l ∈ (unitVertexSpace L).complexSubmodule)
    (hc : ∃ f : FullSpace.Vertex L 0 0 → ℂ, ∀ s, l s = f s • t) :
    ∃ f : FullSpace.Vertex L 0 0 → ℂ, ∀ s, FullSpace.gaugeLaplacian U l s = f s • t := by
  obtain ⟨f, hf⟩ := hc
  have e₁ : (fun x => cartanConj (Real.pi / 4) (l x)) = fun x => scalarHom c (l x) := by
    funext x
    show ComplexMatrix2.conjugateBy (cartanPhase (Real.pi / 4)) (l x) = c • l x
    rw [hf x, conjugateBy_cartanPhase_smul, ← cartanConj_apply, hs.isEigen, smul_comm]
  have e₂ := gaugeLaplacian_map (cartanConj_entrywiseSymmetry (Real.pi / 4)) hU hD hF hl
  have e₃ := gaugeLaplacian_map (scalarHom_entrywiseSymmetry hs.eigenvalue_ne_zero) hU hD hF hl
  rw [e₁, e₃] at e₂
  have h : ∀ x, ∃ z : ℂ, FullSpace.gaugeLaplacian U l x = z • t := fun x =>
    hs.eq_smul_of_eigen _ ((hF.1 l hl).2 x (Set.mem_univ x)) (congrFun e₂ x).symm
  choose g hg using h
  exact ⟨g, hg⟩
theorem massiveHessian_preserves_sector {t : ComplexMatrix2} {c : ℂ} (hs : ChargeSector t c)
    (hL : 0 < L) (hU : IsCartanValued U)
    (hD : CovDiffAndAdjoint U) (hF : CompositesDefined U)
    {B : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L 0 0))
    (hA : FullSpace.complexHessianOperator U (fun b => cartanConj (Real.pi / 4) (B b)) =
      fun b => cartanConj (Real.pi / 4) (FullSpace.complexHessianOperator U B b))
    (hc : ∃ f : FullSpace.PositiveEdge (meshAt L 0 0) → ℂ,
      ∀ s, FullSpace.restrictToPositiveEdges B s = f s • t) :
    ∃ f : FullSpace.PositiveEdge (meshAt L 0 0) → ℂ,
      ∀ s, FullSpace.restrictToPositiveEdges (FullSpace.massiveHessian U B) s = f s • t := by
  obtain ⟨f, hf⟩ := hc
  have e₁ : (fun x => cartanConj (Real.pi / 4) (B x)) = fun x => scalarHom c (B x) := by
    refine oddFunctions_ext (fun b => ?_) (fun b => ?_) fun b hb => ?_
    · show cartanConj _ _ = -cartanConj _ _
      rw [hB.2 b, map_neg]
    · show scalarHom c _ = -scalarHom c _
      rw [hB.2 b, map_neg]
    · show ComplexMatrix2.conjugateBy (cartanPhase (Real.pi / 4)) (B b) = c • B b
      have e : B b = f ⟨b, hb⟩ • t := hf ⟨b, hb⟩
      rw [e, conjugateBy_cartanPhase_smul, ← cartanConj_apply, hs.isEigen, smul_comm]
  have e₂ := massiveHessian_map (cartanConj_entrywiseSymmetry (Real.pi / 4)) hU hD hF hB hA
  have e₃ := massiveHessian_map (scalarHom_entrywiseSymmetry hs.eigenvalue_ne_zero) hU hD hF hB
    (complexHessianOperator_comm_scalar hL c hB)
  rw [e₁, e₃] at e₂
  have h : ∀ x : FullSpace.PositiveEdge (meshAt L 0 0),
      ∃ z : ℂ, FullSpace.massiveHessian U B x.1 = z • t := fun x =>
    hs.eq_smul_of_eigen _ ((hF.2 B hB).2.2.2.1 x.1 x.2) (congrFun e₂ x.1).symm
  choose g hg using h
  exact ⟨g, hg⟩
theorem adjointMatrix_smul_raising (c : ℂ) :
    ComplexMatrix2.adjointMatrix (c • raisingPauli) = conj c • loweringPauli := by
  rw [raisingPauli_eq, loweringPauli_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
theorem adjointMatrix_smul_lowering (c : ℂ) :
    ComplexMatrix2.adjointMatrix (c • loweringPauli) = conj c • raisingPauli := by
  rw [raisingPauli_eq, loweringPauli_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
end Sectors
theorem abelianOperatorSymmetries_holds
    (hPlaquettes : AbelianFieldPlaquettes.Claim)
    (hDirections : UnitGaugeDirections.Claim)
    (hAlgebra : LeftChartAlgebra.AllConditionsHold)
    (hKernel : HessianKernel.KernelProperties)
    (hReal : HessianDeterminants.HessianSymmAndDetsPositive)
    (hSquare : UnitLatticeL2Statement) :
    AbelianOperatorSymmetries := by
  intro L hL θ
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hU : IsCartanValued (FullSpace.abelianLinkField θ) := abelianLinkField_isCartanValued θ
  have hUr : FullSpace.abelianLinkField θ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.compactGaugeGroup :=
    (hPlaquettes L hL θ).abelianLinkField_mem
  have hUc : FullSpace.abelianLinkField θ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (hUr.1 b)).2, hUr.2⟩
  obtain ⟨hD, -, hF, -⟩ := (hDirections L hL).2 _ hUc
  obtain ⟨-, -, hrows, -, hpair, -⟩ := (hKernel L hL 0 0 le_rfl).2 _ hUc
  have hder := (hAlgebra.2.2 L 0 0 hL le_rfl).2.2.2.2.1
  have hreal := ((hReal L hL).1 0 0 le_rfl).2.2 _ hUr
  have hKr : ∀ ι' ι, (FullSpace.complexHessianKernel (FullSpace.abelianLinkField θ) ι' ι).im = 0 :=
    fun ι' ι => hreal _ (basisForm_mem_edgeFormSpace hL0 _ _) (basisForm_hasFiniteEdgeSupport _ _) _
      (basisForm_mem_edgeFormSpace hL0 _ _) (basisForm_hasFiniteEdgeSupport _ _)
  have hAd : ∀ (ϑ : ℝ) {B : FullSpace.Edge L 0 0 → ComplexMatrix2},
      B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) → _ := fun ϑ {B} hB =>
    complexHessianOperator_comm_cartan hL0 hU hUc hder hpair hrows ϑ hB
  have hSites := (hSquare.2 L).2.1.2.1
  have hBonds := (hSquare.2 L).2.2.2.1
  refine
    { cartanPhase_mem := cartanPhase_mem_specialUnitary
      constGauge_mem := fun ϑ x => cartanPhase_mem_specialUnitary ϑ
      laplacian_comm := fun ϑ l hl =>
        gaugeLaplacian_map (cartanConj_entrywiseSymmetry ϑ) hU hD hF fun x _ => hl.1 x
      hessian_comm := fun ϑ B hB => ?_
      laplacian_neutral := fun l hl hc =>
        gaugeLaplacian_preserves_sector chargeSector_neutral hU hD hF (fun x _ => hl.1 x) hc
      laplacian_pos := fun l hl hc =>
        gaugeLaplacian_preserves_sector chargeSector_raising hU hD hF (fun x _ => hl.1 x) hc
      laplacian_neg := fun l hl hc =>
        gaugeLaplacian_preserves_sector chargeSector_lowering hU hD hF (fun x _ => hl.1 x) hc
      hessian_neutral := fun B hB hc =>
        massiveHessian_preserves_sector chargeSector_neutral hL0 hU hD hF hB.1 (hAd _ hB.1) hc
      hessian_pos := fun B hB hc =>
        massiveHessian_preserves_sector chargeSector_raising hL0 hU hD hF hB.1 (hAd _ hB.1) hc
      hessian_neg := fun B hB hc =>
        massiveHessian_preserves_sector chargeSector_lowering hL0 hU hD hF hB.1 (hAd _ hB.1) hc
      star_vertex_l2 := fun l hl => (hSites l hl).2.2.1
      star_form_l2 := fun B hB =>
        ⟨map_mem_complexEdgeForms conjTransposeHom_entrywiseSymmetry hB.1, (hBonds _ hB.2).2.2.1⟩
      laplacian_star := fun l hl =>
        gaugeLaplacian_map conjTransposeHom_entrywiseSymmetry hU hD hF fun x _ => hl.1 x
      hessian_star := fun B hB =>
        massiveHessian_map conjTransposeHom_entrywiseSymmetry hU hD hF hB.1
          (complexHessianOperator_comm_conjTranspose hL0 hKr hB.1)
      star_vertex_pos := fun l hc => ?_
      star_vertex_neg := fun l hc => ?_
      star_form_pos := fun B hc => ?_
      star_form_neg := fun B hc => ?_ }
  · have hK : FullSpace.abelianMassiveHessian θ B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) :=
      (hF.2 B hB.1).2.2.2
    show FullSpace.abelianMassiveHessian θ (FullSpace.adjointForm (fun _ => cartanPhase ϑ) B) =
      FullSpace.adjointForm (fun _ => cartanPhase ϑ) (FullSpace.abelianMassiveHessian θ B)
    rw [adjointForm_const_cartan hL0 ϑ hB.1, adjointForm_const_cartan hL0 ϑ hK]
    exact massiveHessian_map (cartanConj_entrywiseSymmetry ϑ) hU hD hF hB.1 (hAd ϑ hB.1)
  · obtain ⟨c, hc⟩ := hc
    exact ⟨fun s => conj (c s), fun s => by
      show ComplexMatrix2.adjointMatrix (l s) = _
      rw [hc s, adjointMatrix_smul_raising]⟩
  · obtain ⟨c, hc⟩ := hc
    exact ⟨fun s => conj (c s), fun s => by
      show ComplexMatrix2.adjointMatrix (l s) = _
      rw [hc s, adjointMatrix_smul_lowering]⟩
  · obtain ⟨c, hc⟩ := hc
    exact ⟨fun s => conj (c s), fun s => by
      have e : B s.1 = c s • raisingPauli := hc s
      show ComplexMatrix2.adjointMatrix (B s.1) = _
      rw [e, adjointMatrix_smul_raising]⟩
  · obtain ⟨c, hc⟩ := hc
    exact ⟨fun s => conj (c s), fun s => by
      have e : B s.1 = c s • loweringPauli := hc s
      show ComplexMatrix2.adjointMatrix (B s.1) = _
      rw [e, adjointMatrix_smul_lowering]⟩
end YangMills.Construction.Tower.AbelianSymmetryProof
end
