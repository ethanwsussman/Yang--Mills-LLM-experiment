import YangMills.Construction.Towers.CoefficientsOfTheHalfPlaquetteTraceNearAnIndexProof
import YangMills.Construction.Towers.CoefficientsOfTheHessianCurvatureNearAnIndexProof
import YangMills.Construction.Towers.HessianCurvatureKernelOfAFieldIsLocalProof
import YangMills.Construction.Towers.CoefficientsOfTheScaledCovariantDifferenceNearAnIndexProof
import YangMills.Construction.Towers.CoefficientsOfTheTransportDefectNearAnIndex
import YangMills.Construction.Towers.TransportDefectKernelOfAFieldIsLocalProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HolonomyDefectCoeffs
open Matrices
open PeriodicOperators
open BackgroundJets
open Matrices.ComplexMatrix2.FourExpConjugation (bracket)
def pauliComponent (a : Fin 3) (X : ComplexMatrix2) : ℂ :=
  ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
theorem pauliCoeff_eq_pauliComponent (a : Fin 3) {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a X = pauliComponent a X := by
  classical
  simp only [pauliCoeff, dif_pos h]
  rfl
theorem pauliComponent_add (a : Fin 3) (X Y : ComplexMatrix2) :
    pauliComponent a (X + Y) = pauliComponent a X + pauliComponent a Y := by
  fin_cases a <;> simp [pauliComponent] <;> ring
theorem pauliComponent_smul (a : Fin 3) (c : ℂ) (X : ComplexMatrix2) :
    pauliComponent a (c • X) = c * pauliComponent a X := by
  fin_cases a <;> simp [pauliComponent] <;> ring
def cornerTransports (W : Fin 4 → ComplexMatrix2) : Fin 4 → ComplexMatrix2 :=
  ![1, W 0, W 0 * W 1 * (W 2)⁻¹, W 0 * W 1 * (W 2)⁻¹ * (W 3)⁻¹]
theorem det_cornerTransports {W : Fin 4 → ComplexMatrix2} (hW : ∀ i, (W i).det = 1) (i : Fin 4) :
    (cornerTransports W i).det = 1 := by
  have hi : ∀ i, ((W i)⁻¹).det = 1 := fun i => by
    rw [Matrix.det_nonsing_inv, hW i]; simp
  fin_cases i <;> simp [cornerTransports, Matrix.det_mul, hW, hi]
def defectSum (η : ℝ) (T X : Fin 4 → ComplexMatrix2) : ComplexMatrix2 :=
  η⁻¹ • ∑ i, transportSign i • (ComplexMatrix2.conjugateBy (T i) (X i) - X i)
theorem trace_conjugateBy {V A : ComplexMatrix2} (hV : V.det = 1) :
    Matrix.trace (ComplexMatrix2.conjugateBy V A) = Matrix.trace A := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality.trace_conjugateBy <;> assumption
theorem defectSum_mem_traceless (η : ℝ) {T : Fin 4 → ComplexMatrix2} (X : Fin 4 → ComplexMatrix2)
    (hT : ∀ i, (T i).det = 1) :
    defectSum η T X ∈ ComplexMatrix2.traceless := by
  have hterm : ∀ i, ComplexMatrix2.conjugateBy (T i) (X i) - X i ∈ ComplexMatrix2.traceless :=
    fun i => by
      change Matrix.trace _ = 0
      rw [Matrix.trace_sub, trace_conjugateBy (hT i), sub_self]
  have hsum : ∑ i, transportSign i • (ComplexMatrix2.conjugateBy (T i) (X i) - X i) ∈
      ComplexMatrix2.traceless :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hterm i)
  have : defectSum η T X =
      (((η⁻¹ : ℝ) : ℂ)) • ∑ i, transportSign i • (ComplexMatrix2.conjugateBy (T i) (X i) - X i) := by
    ext r s
    simp [defectSum]
  rw [this]
  exact Submodule.smul_mem _ _ hsum
theorem conjugateBy_add (V A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (A + B) =
      ComplexMatrix2.conjugateBy V A + ComplexMatrix2.conjugateBy V B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V A : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (c • A) = c • ComplexMatrix2.conjugateBy V A := by
  simp [ComplexMatrix2.conjugateBy]
theorem defectSum_add (η : ℝ) (T X Y : Fin 4 → ComplexMatrix2) :
    defectSum η T (X + Y) = defectSum η T X + defectSum η T Y := by
  simp only [defectSum, Pi.add_apply, conjugateBy_add, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  abel
theorem defectSum_smul (η : ℝ) (T X : Fin 4 → ComplexMatrix2) (c : ℂ) :
    defectSum η T (c • X) = c • defectSum η T X := by
  simp only [defectSum, Pi.smul_apply, conjugateBy_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_sub, smul_comm (transportSign i) c, smul_comm η⁻¹ c]
variable {L k : ℕ}
def edgeStart (p : Face L k 0) : Fin 4 → Vertex L k 0 :=
  ![p.corner, p.corner + InfiniteLattice.axisStep _ p.lowAxis,
    p.corner + InfiniteLattice.axisStep _ p.highAxis, p.corner]
def edgeAxis (p : Face L k 0) : Fin 4 → Fin 4 :=
  ![p.lowAxis, p.highAxis, p.lowAxis, p.highAxis]
theorem faceEdge_eq_forwardFrom (p : Face L k 0) (i : Fin 4) :
    faceEdge p i = InfiniteLattice.Link.forwardFrom (edgeStart p i) (edgeAxis p i) := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.faceEdge_eq_forwardFrom <;> assumption
def posEdgeOf (p : Face L k 0) (i : Fin 4) : PeriodicOperators.PosEdge L k 0 :=
  ⟨faceEdge p i, edgeAxis p i, by
    rw [faceEdge_eq_forwardFrom]
    simp [InfiniteLattice.Link.forwardFrom]⟩
theorem initial_posEdgeOf (p : Face L k 0) (i : Fin 4) :
    (posEdgeOf p i).1.initial = edgeStart p i := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.initial_posEdgeOfFace <;> assumption
theorem ofCoeffs_posEdge (f : Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ)
    (b : PeriodicOperators.PosEdge L k 0) :
    (edgePauliCoordinates L k 0).ofCoeffs f b.1 = ofPauliCoeffs f b := by apply _root_.YangMills.Construction.Tower.FullSpace.HolonomyDefectLocality.ofCoeffs_posEdge <;> assumption
def edgeValues (f : Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ)
    (p : Face L k 0) : Fin 4 → ComplexMatrix2 :=
  fun i => ofPauliCoeffs f (posEdgeOf p i)
theorem edgeValues_add (f g : Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ)
    (p : Face L k 0) : edgeValues (f + g) p = edgeValues f p + edgeValues g p := by
  funext i
  simp [edgeValues, ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
theorem edgeValues_smul (c : ℂ) (f : Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ)
    (p : Face L k 0) : edgeValues (c • f) p = c • edgeValues f p := by
  funext i
  simp [edgeValues, ofPauliCoeffs, mul_smul, Finset.smul_sum]
def edgeMatrices (U : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) : Fin 4 → ComplexMatrix2 :=
  fun i => U (faceEdge p i)
theorem faceTransports_eq {U : Edge L k 0 → ComplexMatrix2}
    (hU : ∀ b : Edge L k 0, U b.opposite = (U b)⁻¹) (p : Face L k 0) :
    faceTransports U p = cornerTransports (edgeMatrices U p) := by
  funext i
  fin_cases i <;>
    simp [cornerTransports, edgeMatrices, faceTransports, faceVariable, linkHolonomy, faceBoundary,
      faceEdge, faceEdges, hU, mul_assoc]
theorem holonomyDefect_eq {U : Edge L k 0 → ComplexMatrix2}
    (hU : ∀ b : Edge L k 0, U b.opposite = (U b)⁻¹)
    (f : Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ) (p : Face L k 0) :
    holonomyDefect U ((edgePauliCoordinates L k 0).ofCoeffs f) p =
      defectSum (finestMesh L k) (cornerTransports (edgeMatrices U p)) (edgeValues f p) := by
  have h : ∀ i, (edgePauliCoordinates L k 0).ofCoeffs f (faceEdge p i) = edgeValues f p i :=
    fun i => ofCoeffs_posEdge f (posEdgeOf p i)
  simp only [holonomyDefect, defectSum, faceTransports_eq hU, h]
def defectOnCoeffs (U : Edge L k 0 → ComplexMatrix2) :
    (Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ) → Fin 3 × Face L k 0 → ℂ :=
  (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0)) (holonomyDefect U)
theorem defectOnCoeffs_eq {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (f : Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ) (a : Fin 3)
    (p : Face L k 0) :
    defectOnCoeffs U f (a, p) =
      pauliComponent a
        (defectSum (finestMesh L k) (cornerTransports (edgeMatrices U p)) (edgeValues f p)) := by
  change pauliCoeff a (holonomyDefect U ((edgePauliCoordinates L k 0).ofCoeffs f) p) = _
  rw [holonomyDefect_eq hU.2, pauliCoeff_eq_pauliComponent]
  exact defectSum_mem_traceless _ _ (det_cornerTransports fun i => hU.1 _)
theorem holonomyDefectKernel_apply (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (a : Fin 3) (p : Face L k 0)
    (ι : Fin 3 × PeriodicOperators.PosEdge L k 0) :
    holonomyDefectKernel L k U (a, p) ι =
      pauliComponent a (defectSum (finestMesh L k) (cornerTransports (edgeMatrices U p))
        (edgeValues (basisFunction ι : Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ) p)) := by
  classical
  have h := (hK (Fin 3 × PeriodicOperators.PosEdge L k 0) (Fin 3 × Face L k 0)
    (defectOnCoeffs U) ?_ ?_ ?_).2
  · change kernelOfMap (defectOnCoeffs U) (a, p) ι = _
    rw [h]
    exact defectOnCoeffs_eq hU _ a p
  · intro f g
    funext ⟨a, p⟩
    rw [Pi.add_apply, defectOnCoeffs_eq hU, defectOnCoeffs_eq hU, defectOnCoeffs_eq hU,
      edgeValues_add, defectSum_add, pauliComponent_add]
  · intro c f
    funext ⟨a, p⟩
    rw [Pi.smul_apply, defectOnCoeffs_eq hU, defectOnCoeffs_eq hU, edgeValues_smul, defectSum_smul,
      pauliComponent_smul, smul_eq_mul]
  · rintro ⟨a, p⟩
    refine ⟨Finset.univ.image fun q : Fin 3 × Fin 4 => (q.1, posEdgeOf p q.2), fun f g h => ?_⟩
    rw [defectOnCoeffs_eq hU, defectOnCoeffs_eq hU]
    have : edgeValues f p = edgeValues g p := by
      funext i
      simp only [edgeValues, ofPauliCoeffs]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [h (e, posEdgeOf p i) (Finset.mem_image.2 ⟨(e, i), Finset.mem_univ _, rfl⟩)]
    rw [this]
def pauliComponentForm (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun := pauliComponent a
  map_add' := pauliComponent_add a
  map_smul' c X := by simpa using pauliComponent_smul a c X
theorem pauliComponentForm_apply (a : Fin 3) (X : ComplexMatrix2) :
    pauliComponentForm a X = pauliComponent a X := rfl
def pauliComponentBound : ℝ := ∑ a, ‖LinearMap.toContinuousLinearMap (pauliComponentForm a)‖
theorem pauliComponentBound_nonneg : 0 ≤ pauliComponentBound :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem norm_pauliEntryForm_le (a : Fin 3) (X : ComplexMatrix2) :
    ‖pauliComponentForm a X‖ ≤ pauliComponentBound * ‖X‖ := by
  have h := (LinearMap.toContinuousLinearMap (pauliComponentForm a)).le_opNorm X
  have h' : ‖LinearMap.toContinuousLinearMap (pauliComponentForm a)‖ ≤ pauliComponentBound :=
    Finset.single_le_sum (f := fun a => ‖LinearMap.toContinuousLinearMap (pauliComponentForm a)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  calc ‖pauliComponentForm a X‖ ≤ ‖LinearMap.toContinuousLinearMap (pauliComponentForm a)‖ * ‖X‖ := h
    _ ≤ pauliComponentBound * ‖X‖ := by gcongr
def pauliNormSum : ℝ := ∑ e, ‖ComplexMatrix2.pauliFamily e‖
theorem pauliNormSum_nonneg : 0 ≤ pauliNormSum := Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem norm_ofPauliCoeffs_le {σ : Type} (f : Fin 3 × σ → ℂ) (b : σ) {m : ℝ}
    (h : ∀ e, ‖f (e, b)‖ ≤ m) : ‖ofPauliCoeffs f b‖ ≤ pauliNormSum * m := by apply _root_.YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex.norm_ofPauliCoeffs_le <;> assumption
theorem norm_bracket_le_mul (X Y : ComplexMatrix2) : ‖bracket X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by apply _root_.YangMills.SharedProofs.p42284 <;> assumption
theorem add_bracket (X X' Y : ComplexMatrix2) :
    bracket (X + X') Y = bracket X Y + bracket X' Y := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelCoeffs.bracket_add_fst <;> assumption
theorem bracket_add (X Y Y' : ComplexMatrix2) :
    bracket X (Y + Y') = bracket X Y + bracket X Y' := by apply _root_.YangMills.Construction.Tower.FullSpace.CovariantDifferenceCoeffs.bracket_add_right <;> assumption
theorem smul_bracket (c : ℂ) (X Y : ComplexMatrix2) : bracket (c • X) Y = c • bracket X Y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]
theorem bracket_smul (c : ℂ) (X Y : ComplexMatrix2) : bracket X (c • Y) = c • bracket X Y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]
def halfCommutators (Z Z' : Fin 4 → ComplexMatrix2) : ComplexMatrix2 :=
  (1 / 2 : ℂ) • ∑ i, ∑ i' ∈ Finset.Ioi i, (Z i * Z' i' - Z' i' * Z i)
theorem halfCommutators_add_left (Z₁ Z₂ Z' : Fin 4 → ComplexMatrix2) :
    halfCommutators (Z₁ + Z₂) Z' = halfCommutators Z₁ Z' + halfCommutators Z₂ Z' := by
  simp only [halfCommutators, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, add_mul, mul_add]
  abel
theorem halfCommutators_add_right (Z Z₁ Z₂ : Fin 4 → ComplexMatrix2) :
    halfCommutators Z (Z₁ + Z₂) = halfCommutators Z Z₁ + halfCommutators Z Z₂ := by
  simp only [halfCommutators, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, add_mul, mul_add]
  abel
theorem halfCommutators_smul_left (c : ℂ) (Z Z' : Fin 4 → ComplexMatrix2) :
    halfCommutators (c • Z) Z' = c • halfCommutators Z Z' := by
  simp only [halfCommutators]
  rw [smul_comm]
  congr 1
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_mul_assoc, mul_smul_comm, smul_sub]
theorem halfCommutators_smul_right (c : ℂ) (Z Z' : Fin 4 → ComplexMatrix2) :
    halfCommutators Z (c • Z') = c • halfCommutators Z Z' := by
  simp only [halfCommutators]
  rw [smul_comm]
  congr 1
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_mul_assoc, mul_smul_comm, smul_sub]
theorem norm_halfCommutators_le {Z Z' : Fin 4 → ComplexMatrix2} {A : ℝ} (hA : 0 ≤ A)
    (hZ : ∀ j, ‖Z j‖ ≤ A) (hZ' : ∀ j, ‖Z' j‖ ≤ A) : ‖halfCommutators Z Z'‖ ≤ 16 * A ^ 2 := by
  have hterm : ∀ i j, ‖Z i * Z' j - Z' j * Z i‖ ≤ 2 * A ^ 2 := fun i j => by
    calc ‖Z i * Z' j - Z' j * Z i‖ ≤ ‖Z i * Z' j‖ + ‖Z' j * Z i‖ := norm_sub_le _ _
      _ ≤ ‖Z i‖ * ‖Z' j‖ + ‖Z' j‖ * ‖Z i‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ A * A + A * A := by
          gcongr
          exacts [hZ i, hZ' j, hZ' j, hZ i]
      _ = 2 * A ^ 2 := by ring
  have hin : ∀ i, ‖∑ i' ∈ Finset.Ioi i, (Z i * Z' i' - Z' i' * Z i)‖ ≤ 8 * A ^ 2 := fun i => by
    calc ‖∑ i' ∈ Finset.Ioi i, (Z i * Z' i' - Z' i' * Z i)‖
        ≤ ∑ _i' ∈ Finset.Ioi i, 2 * A ^ 2 := norm_sum_le_of_le _ fun j _ => hterm i j
      _ = ((Finset.Ioi i).card : ℝ) * (2 * A ^ 2) := by simp
      _ ≤ 4 * (2 * A ^ 2) := by
          have : (Finset.Ioi i).card ≤ 4 := by
            simpa using Finset.card_le_univ (Finset.Ioi i)
          have h' : ((Finset.Ioi i).card : ℝ) ≤ 4 := by exact_mod_cast this
          gcongr
      _ = 8 * A ^ 2 := by ring
  have hout : ‖∑ i, ∑ i' ∈ Finset.Ioi i, (Z i * Z' i' - Z' i' * Z i)‖ ≤ 32 * A ^ 2 := by
    calc _ ≤ ∑ _i : Fin 4, 8 * A ^ 2 := norm_sum_le_of_le _ fun i _ => hin i
      _ = 32 * A ^ 2 := by simp; ring
  rw [halfCommutators, norm_smul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  linarith
def secondOrderTerm (Z Z' : Fin 4 → ComplexMatrix2) (Y : ComplexMatrix2) : ComplexMatrix2 :=
  (1 / 2 : ℂ) • (bracket (∑ j, Z j) (bracket (∑ j, Z' j) Y) +
    bracket (∑ j, Z' j) (bracket (∑ j, Z j) Y)) +
      bracket (halfCommutators Z Z' + halfCommutators Z' Z) Y
theorem secondOrderTerm_comm (Z Z' : Fin 4 → ComplexMatrix2) (Y : ComplexMatrix2) :
    secondOrderTerm Z Z' Y = secondOrderTerm Z' Z Y := by
  simp only [secondOrderTerm]
  rw [add_comm (bracket (∑ j, Z j) _), add_comm (halfCommutators Z Z')]
theorem secondOrderTerm_add_left (Z₁ Z₂ Z' : Fin 4 → ComplexMatrix2) (Y : ComplexMatrix2) :
    secondOrderTerm (Z₁ + Z₂) Z' Y = secondOrderTerm Z₁ Z' Y + secondOrderTerm Z₂ Z' Y := by
  simp only [secondOrderTerm, halfCommutators_add_left, halfCommutators_add_right, Pi.add_apply,
    Finset.sum_add_distrib, add_bracket, bracket_add, smul_add]
  abel
theorem secondOrderTerm_smul_left (c : ℂ) (Z Z' : Fin 4 → ComplexMatrix2) (Y : ComplexMatrix2) :
    secondOrderTerm (c • Z) Z' Y = c • secondOrderTerm Z Z' Y := by
  simp only [secondOrderTerm, halfCommutators_smul_left, halfCommutators_smul_right, Pi.smul_apply,
    ← Finset.smul_sum, smul_bracket, bracket_smul, add_bracket]
  module
theorem half_secondOrderTerm_self (Z : Fin 4 → ComplexMatrix2) (Y : ComplexMatrix2) :
    (1 / 2 : ℂ) • secondOrderTerm Z Z Y =
      (1 / 2 : ℂ) • bracket (∑ j, Z j) (bracket (∑ j, Z j) Y) +
        bracket (ComplexMatrix2.halfCommutatorSum Z) Y := by
  have h : halfCommutators Z Z = ComplexMatrix2.halfCommutatorSum Z := rfl
  simp only [secondOrderTerm, h, add_bracket]
  module
theorem norm_sum_fin_four_le {Z : Fin 4 → ComplexMatrix2} {A : ℝ} (hZ : ∀ j, ‖Z j‖ ≤ A) :
    ‖∑ j, Z j‖ ≤ 4 * A := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelCoeffs.norm_sum_fin_four_le <;> assumption
theorem norm_bracket_sum_le_mul {Z : Fin 4 → ComplexMatrix2} {A : ℝ} (hZ : ∀ j, ‖Z j‖ ≤ A)
    (Y : ComplexMatrix2) : ‖bracket (∑ j, Z j) Y‖ ≤ 8 * A * ‖Y‖ := by
  calc ‖bracket (∑ j, Z j) Y‖ ≤ 2 * ‖∑ j, Z j‖ * ‖Y‖ := norm_bracket_le_mul _ _
    _ ≤ 2 * (4 * A) * ‖Y‖ := by
        have := norm_sum_fin_four_le hZ
        gcongr
    _ = 8 * A * ‖Y‖ := by ring
theorem norm_secondOrderTerm_le {Z Z' : Fin 4 → ComplexMatrix2} {A : ℝ} (hA : 0 ≤ A)
    (hZ : ∀ j, ‖Z j‖ ≤ A) (hZ' : ∀ j, ‖Z' j‖ ≤ A) (Y : ComplexMatrix2) :
    ‖secondOrderTerm Z Z' Y‖ ≤ 128 * A ^ 2 * ‖Y‖ := by
  have hb₁ : ‖bracket (∑ j, Z j) (bracket (∑ j, Z' j) Y)‖ ≤ 64 * A ^ 2 * ‖Y‖ := by
    calc _ ≤ 8 * A * ‖bracket (∑ j, Z' j) Y‖ := norm_bracket_sum_le_mul hZ _
      _ ≤ 8 * A * (8 * A * ‖Y‖) := by
          have := norm_bracket_sum_le_mul hZ' Y
          gcongr
      _ = 64 * A ^ 2 * ‖Y‖ := by ring
  have hb₂ : ‖bracket (∑ j, Z' j) (bracket (∑ j, Z j) Y)‖ ≤ 64 * A ^ 2 * ‖Y‖ := by
    calc _ ≤ 8 * A * ‖bracket (∑ j, Z j) Y‖ := norm_bracket_sum_le_mul hZ' _
      _ ≤ 8 * A * (8 * A * ‖Y‖) := by
          have := norm_bracket_sum_le_mul hZ Y
          gcongr
      _ = 64 * A ^ 2 * ‖Y‖ := by ring
  have hc : ‖bracket (halfCommutators Z Z' + halfCommutators Z' Z) Y‖ ≤ 64 * A ^ 2 * ‖Y‖ := by
    calc _ ≤ 2 * ‖halfCommutators Z Z' + halfCommutators Z' Z‖ * ‖Y‖ := norm_bracket_le_mul _ _
      _ ≤ 2 * (16 * A ^ 2 + 16 * A ^ 2) * ‖Y‖ := by
          have h₁ := norm_halfCommutators_le hA hZ hZ'
          have h₂ := norm_halfCommutators_le hA hZ' hZ
          have := norm_add_le (halfCommutators Z Z') (halfCommutators Z' Z)
          gcongr
          linarith
      _ = 64 * A ^ 2 * ‖Y‖ := by ring
  have hh : ‖(1 / 2 : ℂ) • (bracket (∑ j, Z j) (bracket (∑ j, Z' j) Y) +
      bracket (∑ j, Z' j) (bracket (∑ j, Z j) Y))‖ ≤ 64 * A ^ 2 * ‖Y‖ := by
    rw [norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    have := norm_add_le (bracket (∑ j, Z j) (bracket (∑ j, Z' j) Y))
      (bracket (∑ j, Z' j) (bracket (∑ j, Z j) Y))
    linarith
  calc ‖secondOrderTerm Z Z' Y‖ ≤ _ := norm_add_le _ _
    _ ≤ 128 * A ^ 2 * ‖Y‖ := by linarith
theorem conjugateBy_prod_exp_expansion
    (hX : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    (Z : Fin 4 → ComplexMatrix2) (Y : ComplexMatrix2) (h : ∑ j, ‖Z j‖ ≤ 1) :
    ‖ComplexMatrix2.conjugateBy (List.ofFn fun j => ComplexMatrix2.matExp (Z j)).prod Y - Y -
        bracket (∑ j, Z j) Y - (1 / 2 : ℂ) • secondOrderTerm Z Z Y‖ ≤
      10 * Real.exp 1 ^ 2 * (∑ j, ‖Z j‖) ^ 3 * ‖Y‖ := by
  rw [half_secondOrderTerm_self]
  exact (hX Z Y _ _ _ _ rfl h rfl rfl rfl).1
section Forms
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def firstOrderForm (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) (Z : Fin 4 → V →ₗ[ℂ] ComplexMatrix2)
    (Y : ComplexMatrix2) : V →ₗ[ℂ] ℂ where
  toFun ζ := φ (bracket (∑ j, Z j ζ) Y)
  map_add' ζ ζ' := by
    simp only [map_add, Finset.sum_add_distrib, add_bracket]
  map_smul' c ζ := by
    simp only [map_smul, ← Finset.smul_sum, smul_bracket, RingHom.id_apply, smul_eq_mul]
def secondOrderForm (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) (Z : Fin 4 → V →ₗ[ℂ] ComplexMatrix2)
    (Y : ComplexMatrix2) : V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun ζ ζ' => φ (secondOrderTerm (fun j => Z j ζ) (fun j => Z j ζ') Y))
    (fun ζ₁ ζ₂ ζ' => by
      have : (fun j => Z j (ζ₁ + ζ₂)) = (fun j => Z j ζ₁) + fun j => Z j ζ₂ := by
        funext j
        simp
      rw [this, secondOrderTerm_add_left, map_add])
    (fun c ζ ζ' => by
      have : (fun j => Z j (c • ζ)) = c • fun j => Z j ζ := by
        funext j
        simp
      rw [this, secondOrderTerm_smul_left, map_smul])
    (fun ζ ζ₁ ζ₂ => by
      have : (fun j => Z j (ζ₁ + ζ₂)) = (fun j => Z j ζ₁) + fun j => Z j ζ₂ := by
        funext j
        simp
      rw [this, secondOrderTerm_comm, secondOrderTerm_add_left, map_add, secondOrderTerm_comm,
        secondOrderTerm_comm (fun j => Z j ζ₂)])
    (fun c ζ ζ' => by
      have : (fun j => Z j (c • ζ')) = c • fun j => Z j ζ' := by
        funext j
        simp
      rw [this, secondOrderTerm_comm, secondOrderTerm_smul_left, map_smul, secondOrderTerm_comm])
theorem firstOrderForm_apply (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) (Z : Fin 4 → V →ₗ[ℂ] ComplexMatrix2)
    (Y : ComplexMatrix2) (ζ : V) :
    firstOrderForm φ Z Y ζ = φ (bracket (∑ j, Z j ζ) Y) := rfl
theorem secondOrderForm_apply (φ : ComplexMatrix2 →ₗ[ℂ] ℂ) (Z : Fin 4 → V →ₗ[ℂ] ComplexMatrix2)
    (Y : ComplexMatrix2) (ζ ζ' : V) :
    secondOrderForm φ Z Y ζ ζ' = φ (secondOrderTerm (fun j => Z j ζ) (fun j => Z j ζ') Y) := rfl
end Forms
def exponentCoeff : Fin 4 → Fin 4 → ℂ :=
  ![![0, 0, 0, 0], ![Complex.I, 0, 0, 0], ![Complex.I, Complex.I, -Complex.I, 0],
    ![Complex.I, Complex.I, -Complex.I, -Complex.I]]
theorem norm_exponentCoeff_le (l j : Fin 4) : ‖exponentCoeff l j‖ ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelCoeffs.norm_exponentCoeff_le <;> assumption
theorem inv_matExp_I_smul (X : ComplexMatrix2) :
    (ComplexMatrix2.matExp (Complex.I • X))⁻¹ = ComplexMatrix2.matExp ((-Complex.I) • X) := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelCoeffs.inv_matExp_I_smul <;> assumption
theorem cornerTransports_matExp (x : Fin 4 → ComplexMatrix2) (l : Fin 4) :
    cornerTransports (fun j => ComplexMatrix2.matExp (Complex.I • x j)) l =
      (List.ofFn fun j => ComplexMatrix2.matExp (exponentCoeff l j • x j)).prod := by
  fin_cases l <;>
    simp [cornerTransports, exponentCoeff, List.ofFn_succ, inv_matExp_I_smul, mul_assoc]
abbrev CoeffField (L k : ℕ) : Type := Fin 3 × PeriodicOperators.PosEdge L k 0 → ℂ
def edgeValueMap (b : PeriodicOperators.PosEdge L k 0) : CoeffField L k →ₗ[ℂ] ComplexMatrix2 where
  toFun ζ := ofPauliCoeffs ζ b
  map_add' f g := by simp [ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [ofPauliCoeffs, mul_smul, Finset.smul_sum]
def exponentMap (p : Face L k 0) (l j : Fin 4) : CoeffField L k →ₗ[ℂ] ComplexMatrix2 :=
  exponentCoeff l j • edgeValueMap (posEdgeOf p j)
theorem exponentMap_apply (p : Face L k 0) (l j : Fin 4) (ζ : CoeffField L k) :
    exponentMap p l j ζ = exponentCoeff l j • ofPauliCoeffs ζ (posEdgeOf p j) := rfl
theorem norm_exponentMap_le (p : Face L k 0) (l j : Fin 4) (ζ : CoeffField L k) {m : ℝ}
    (h : ‖ofPauliCoeffs ζ (posEdgeOf p j)‖ ≤ m) : ‖exponentMap p l j ζ‖ ≤ m := by
  rw [exponentMap_apply, norm_smul]
  calc _ ≤ 1 * ‖ofPauliCoeffs ζ (posEdgeOf p j)‖ :=
        mul_le_mul_of_nonneg_right (norm_exponentCoeff_le l j) (norm_nonneg _)
    _ ≤ m := by simpa using h
def transportProd (p : Face L k 0) (l : Fin 4) (ζ : CoeffField L k) : ComplexMatrix2 :=
  (List.ofFn fun j => ComplexMatrix2.matExp (exponentMap p l j ζ)).prod
theorem transportProd_zero (p : Face L k 0) (l : Fin 4) : transportProd p l 0 = 1 := by
  simp [transportProd, List.ofFn_succ, NormedSpace.exp_zero]
theorem edgeMatrices_gaugeFieldOfForm (ζ : CoeffField L k) (p : Face L k 0) :
    edgeMatrices (gaugeFieldOfForm L k ζ) p =
      fun j => ComplexMatrix2.matExp (Complex.I • ofPauliCoeffs ζ (posEdgeOf p j)) := by
  classical
  funext j
  have hb : (faceEdge p j).IsPositivelyOriented := (posEdgeOf p j).2
  have h := ofCoeffs_posEdge ζ (posEdgeOf p j)
  simp only [edgeMatrices, gaugeFieldOfForm, expForm, expTwist, if_pos hb, Pi.one_apply,
    mul_one]
  exact congrArg (fun X => ComplexMatrix2.matExp (Complex.I • X)) h
theorem cornerTransports_gaugeFieldOfForm (ζ : CoeffField L k) (p : Face L k 0) (l : Fin 4) :
    cornerTransports (edgeMatrices (gaugeFieldOfForm L k ζ) p) l = transportProd p l ζ := by
  rw [edgeMatrices_gaugeFieldOfForm]
  exact cornerTransports_matExp _ l
def signedInvMesh (L k : ℕ) (l : Fin 4) : ℂ :=
  (((finestMesh L k)⁻¹ : ℝ) : ℂ) * transportSign l
theorem norm_signedInvMesh (hη : 0 < finestMesh L k) (l : Fin 4) :
    ‖signedInvMesh L k l‖ = (finestMesh L k)⁻¹ := by
  have hs : ‖transportSign l‖ = 1 := by
    fin_cases l <;> simp [transportSign]
  rw [signedInvMesh, norm_mul, hs, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  exact inv_nonneg.2 hη.le
theorem norm_sum_signedInvMesh_le (hη : 0 < finestMesh L k) (t : Fin 4 → ℂ) {B : ℝ}
    (h : ∀ l, ‖t l‖ ≤ B) :
    ‖∑ l, signedInvMesh L k l * t l‖ ≤ 4 * ((finestMesh L k)⁻¹ * B) := by
  calc ‖∑ l, signedInvMesh L k l * t l‖
      ≤ ∑ _l : Fin 4, (finestMesh L k)⁻¹ * B := norm_sum_le_of_le _ fun l _ => by
        rw [norm_mul, norm_signedInvMesh hη]
        exact mul_le_mul_of_nonneg_left (h l) (inv_nonneg.2 hη.le)
    _ = 4 * ((finestMesh L k)⁻¹ * B) := by simp
theorem pauliComponent_defectSum (η : ℝ) (T X : Fin 4 → ComplexMatrix2) (a : Fin 3) :
    pauliComponent a (defectSum η T X) =
      ∑ l, ((η⁻¹ : ℝ) : ℂ) * transportSign l *
        pauliComponentForm a (ComplexMatrix2.conjugateBy (T l) (X l) - X l) := by
  have e : defectSum η T X =
      ((η⁻¹ : ℝ) : ℂ) • ∑ i, transportSign i • (ComplexMatrix2.conjugateBy (T i) (X i) - X i) := by
    ext r s
    simp [defectSum]
  rw [e, ← pauliComponentForm_apply, map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, smul_eq_mul, mul_assoc]
theorem holonomyDefectKernel_gaugeField (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hcfg : ∀ ζ : CoeffField L k,
      gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (a : Fin 3) (p : Face L k 0) (ι : Fin 3 × PeriodicOperators.PosEdge L k 0)
    (ζ : CoeffField L k) :
    holonomyDefectKernel L k (gaugeFieldOfForm L k ζ) (a, p) ι =
      ∑ l, signedInvMesh L k l * pauliComponentForm a
        (ComplexMatrix2.conjugateBy (transportProd p l ζ)
            (edgeValues (basisFunction ι : CoeffField L k) p l) -
          edgeValues (basisFunction ι : CoeffField L k) p l) := by
  rw [holonomyDefectKernel_apply hK (hcfg ζ), pauliComponent_defectSum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [cornerTransports_gaugeFieldOfForm, signedInvMesh]
def firstCoeffForm (p : Face L k 0) (a : Fin 3) (Y : Fin 4 → ComplexMatrix2) :
    CoeffField L k →ₗ[ℂ] ℂ :=
  ∑ l, signedInvMesh L k l • firstOrderForm (pauliComponentForm a) (exponentMap p l) (Y l)
def secondCoeffForm (p : Face L k 0) (a : Fin 3) (Y : Fin 4 → ComplexMatrix2) :
    CoeffField L k →ₗ[ℂ] CoeffField L k →ₗ[ℂ] ℂ :=
  ∑ l, signedInvMesh L k l • secondOrderForm (pauliComponentForm a) (exponentMap p l) (Y l)
theorem firstCoeffForm_apply (p : Face L k 0) (a : Fin 3) (Y : Fin 4 → ComplexMatrix2)
    (ζ : CoeffField L k) :
    firstCoeffForm p a Y ζ =
      ∑ l, signedInvMesh L k l * pauliComponentForm a (bracket (∑ j, exponentMap p l j ζ) (Y l)) := by
  simp only [firstCoeffForm, LinearMap.sum_apply, LinearMap.smul_apply, firstOrderForm_apply,
    smul_eq_mul]
theorem secondCoeffForm_apply (p : Face L k 0) (a : Fin 3) (Y : Fin 4 → ComplexMatrix2)
    (ζ ζ' : CoeffField L k) :
    secondCoeffForm p a Y ζ ζ' = ∑ l, signedInvMesh L k l * pauliComponentForm a
      (secondOrderTerm (fun j => exponentMap p l j ζ) (fun j => exponentMap p l j ζ') (Y l)) := by
  simp only [secondCoeffForm, LinearMap.sum_apply, LinearMap.smul_apply, secondOrderForm_apply,
    smul_eq_mul]
def cubicRemainderConst (L k : ℕ) (Y : Fin 4 → ComplexMatrix2) : ℝ :=
  4 * ((finestMesh L k)⁻¹ * (pauliComponentBound * (10 * Real.exp 1 ^ 2 * (4 * pauliNormSum) ^ 3 *
    ∑ l, ‖Y l‖)))
theorem holonomyDefectKernel_cubic_remainder (hη : 0 < finestMesh L k)
    (hX : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hcfg : ∀ ζ : CoeffField L k,
      gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (a : Fin 3) (p : Face L k 0) (ι : Fin 3 × PeriodicOperators.PosEdge L k 0)
    (ζ : CoeffField L k) {m : ℝ} (hm : 0 ≤ m) (hr : 4 * (pauliNormSum * m) ≤ 1)
    (hζ : ∀ j e, ‖ζ (e, posEdgeOf p j)‖ ≤ m) :
    ‖holonomyDefectKernel L k (gaugeFieldOfForm L k ζ) (a, p) ι -
        holonomyDefectKernel L k (gaugeFieldOfForm L k 0) (a, p) ι -
        firstCoeffForm p a (edgeValues (basisFunction ι : CoeffField L k) p) ζ -
        (1 / 2 : ℂ) * secondCoeffForm p a (edgeValues (basisFunction ι : CoeffField L k) p) ζ ζ‖ ≤
      cubicRemainderConst L k (edgeValues (basisFunction ι : CoeffField L k) p) * m ^ 3 := by
  set Y := edgeValues (basisFunction ι : CoeffField L k) p with hY
  have e0 : holonomyDefectKernel L k (gaugeFieldOfForm L k 0) (a, p) ι = 0 := by
    refine (holonomyDefectKernel_gaugeField hK hcfg a p ι (0 : CoeffField L k)).trans ?_
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [transportProd_zero, ComplexMatrix2.conjugateBy]
  have e : holonomyDefectKernel L k (gaugeFieldOfForm L k ζ) (a, p) ι -
        holonomyDefectKernel L k (gaugeFieldOfForm L k 0) (a, p) ι -
        firstCoeffForm p a Y ζ - (1 / 2 : ℂ) * secondCoeffForm p a Y ζ ζ =
      ∑ l, signedInvMesh L k l * pauliComponentForm a
        (ComplexMatrix2.conjugateBy (transportProd p l ζ) (Y l) - Y l -
          bracket (∑ j, exponentMap p l j ζ) (Y l) -
          (1 / 2 : ℂ) • secondOrderTerm (fun j => exponentMap p l j ζ)
            (fun j => exponentMap p l j ζ) (Y l)) := by
    rw [holonomyDefectKernel_gaugeField hK hcfg a p ι ζ, e0, firstCoeffForm_apply,
      secondCoeffForm_apply, sub_zero, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  rw [e]
  have hϱ : ∀ l, ∑ j, ‖exponentMap p l j ζ‖ ≤ 4 * (pauliNormSum * m) := fun l => by
    calc ∑ j, ‖exponentMap p l j ζ‖ ≤ ∑ _j : Fin 4, pauliNormSum * m :=
          Finset.sum_le_sum fun j _ =>
            norm_exponentMap_le p l j ζ (norm_ofPauliCoeffs_le ζ _ fun e => hζ j e)
      _ = 4 * (pauliNormSum * m) := by simp
  have hP := pauliNormSum_nonneg
  have hE := pauliComponentBound_nonneg
  have hterm : ∀ l, ‖pauliComponentForm a
      (ComplexMatrix2.conjugateBy (transportProd p l ζ) (Y l) - Y l -
        bracket (∑ j, exponentMap p l j ζ) (Y l) -
        (1 / 2 : ℂ) • secondOrderTerm (fun j => exponentMap p l j ζ)
          (fun j => exponentMap p l j ζ) (Y l))‖ ≤
      pauliComponentBound * (10 * Real.exp 1 ^ 2 * (4 * pauliNormSum) ^ 3 * ∑ l, ‖Y l‖) * m ^ 3 :=
    fun l => by
    have h1 := conjugateBy_prod_exp_expansion hX (fun j => exponentMap p l j ζ) (Y l)
      ((hϱ l).trans hr)
    have h2 : (∑ j, ‖exponentMap p l j ζ‖) ^ 3 ≤ (4 * (pauliNormSum * m)) ^ 3 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hϱ l) 3
    have h3 : ‖Y l‖ ≤ ∑ l, ‖Y l‖ :=
      Finset.single_le_sum (f := fun l => ‖Y l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
    calc _ ≤ pauliComponentBound * _ := norm_pauliEntryForm_le a _
      _ ≤ pauliComponentBound *
          (10 * Real.exp 1 ^ 2 * (4 * (pauliNormSum * m)) ^ 3 * ∑ l, ‖Y l‖) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) hE
          gcongr
      _ = _ := by ring
  refine (norm_sum_signedInvMesh_le hη _ hterm).trans (le_of_eq ?_)
  simp only [cubicRemainderConst]
  ring
theorem coeffOne_coeffTwo_eq (hη : 0 < finestMesh L k)
    (hT : ExpansionCoefficients.Claim)
    (hX : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hcfg : ∀ ζ : CoeffField L k,
      gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (hB : IsPeriodic (colourEdges L k 0))
    (hP : IsPeriodic (colourFaces L k 0))
    (hloc : IsLocalOpFun (remainderIndex L k) (colourEdges L k 0)
      (colourFaces L k 0)
      (fun f => holonomyDefectKernel L k (gaugeFieldOfForm L k f)))
    (a : Fin 3) (p : Face L k 0) (ι : Fin 3 × PeriodicOperators.PosEdge L k 0)
    (ζ ζ' : CoeffField L k) :
    coeffOne (remainderIndex L k) (colourEdges L k 0) (colourFaces L k 0)
        (fun f => holonomyDefectKernel L k (gaugeFieldOfForm L k f)) ζ (a, p) ι =
      firstCoeffForm p a (edgeValues (basisFunction ι : CoeffField L k) p) ζ ∧
    coeffTwo (remainderIndex L k) (colourEdges L k 0) (colourFaces L k 0)
        (fun f => holonomyDefectKernel L k (gaugeFieldOfForm L k f)) ζ ζ' (a, p) ι =
      secondCoeffForm p a (edgeValues (basisFunction ι : CoeffField L k) p) ζ ζ' := by
  have hP0 := pauliNormSum_nonneg
  set Y := edgeValues (basisFunction ι : CoeffField L k) p with hY
  have hcongr : ∀ ζ₁ ζ₂ : CoeffField L k,
      (∀ κ ∈ Set.range fun q : Fin 3 × Fin 4 =>
        ((q.1, posEdgeOf p q.2) : Fin 3 × PeriodicOperators.PosEdge L k 0), ζ₁ κ = ζ₂ κ) →
      ∀ l j, exponentMap p l j ζ₁ = exponentMap p l j ζ₂ := fun ζ₁ ζ₂ h l j => by
    simp only [exponentMap_apply, ofPauliCoeffs]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [h (e, posEdgeOf p j) ⟨(e, j), rfl⟩]
  have hsym : ∀ ζ₁ ζ₂ : CoeffField L k,
      secondCoeffForm p a Y ζ₁ ζ₂ = secondCoeffForm p a Y ζ₂ ζ₁ := by
    intro ζ₁ ζ₂
    rw [secondCoeffForm_apply, secondCoeffForm_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [secondOrderTerm_comm]
  have hread : ∀ ζ₁ ζ₂ : CoeffField L k, (∀ κ ∈ Set.range fun q : Fin 3 × Fin 4 =>
        ((q.1, posEdgeOf p q.2) : Fin 3 × PeriodicOperators.PosEdge L k 0), ζ₁ κ = ζ₂ κ) →
      firstCoeffForm p a Y ζ₁ = firstCoeffForm p a Y ζ₂ ∧
        ∀ ξ : CoeffField L k, secondCoeffForm p a Y ζ₁ ξ = secondCoeffForm p a Y ζ₂ ξ := by
    intro ζ₁ ζ₂ h
    have hc := hcongr ζ₁ ζ₂ h
    refine ⟨?_, fun ξ => ?_⟩
    · simp only [firstCoeffForm_apply, hc]
    · simp only [secondCoeffForm_apply, hc]
  have hbd : ∀ (ζ₁ : CoeffField L k) (m : ℝ), m ≤ 1 / (4 * pauliNormSum + 1) →
      (∀ κ ∈ Set.range fun q : Fin 3 × Fin 4 =>
        ((q.1, posEdgeOf p q.2) : Fin 3 × PeriodicOperators.PosEdge L k 0), ‖ζ₁ κ‖ ≤ m) →
      ‖holonomyDefectKernel L k (gaugeFieldOfForm L k ζ₁) (a, p) ι -
        holonomyDefectKernel L k (gaugeFieldOfForm L k 0) (a, p) ι -
        firstCoeffForm p a Y ζ₁ - (1 / 2 : ℂ) * secondCoeffForm p a Y ζ₁ ζ₁‖ ≤
      cubicRemainderConst L k Y * m ^ 3 := by
    intro ζ₁ m hm h
    have hm0 : 0 ≤ m := (norm_nonneg _).trans (h (0, posEdgeOf p 0) ⟨(0, 0), rfl⟩)
    have hr : 4 * (pauliNormSum * m) ≤ 1 := by
      have h1 : (4 * pauliNormSum + 1) * m ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * pauliNormSum + 1)
        rwa [mul_one_div_cancel (by positivity)] at this
      nlinarith
    exact holonomyDefectKernel_cubic_remainder hη hX hK hcfg a p ι ζ₁ hm0 hr
      fun j e => h _ ⟨(e, j), rfl⟩
  exact hT (remainderIndex L k) (colourEdges L k 0) (colourFaces L k 0) hB hB hP _ hloc
    (a, p) ι (Set.range fun q : Fin 3 × Fin 4 =>
      ((q.1, posEdgeOf p q.2) : Fin 3 × PeriodicOperators.PosEdge L k 0)) (Set.finite_range _)
    (firstCoeffForm p a Y) (secondCoeffForm p a Y) (1 / (4 * pauliNormSum + 1))
    (cubicRemainderConst L k Y) (by positivity) hsym hread hbd ζ ζ'
theorem withinBox_corner (hη : 0 < finestMesh L k) (p : Face L k 0) (i : Fin 4) :
    WithinBox (2 * finestMesh L k) (posEdgeOf p i).1.initial p.corner := by
  rw [initial_posEdgeOf]
  have hs : ∀ ν μ, |((InfiniteLattice.axisStep (meshAt L k 0) ν : Vertex L k 0) :
      InfiniteLattice.AmbientSpace) μ| ≤ 2 * finestMesh L k := fun ν μ => by
    change |(Pi.single ν (finestMesh L k) : InfiniteLattice.AmbientSpace) μ| ≤ _
    by_cases h : μ = ν
    · subst h
      rw [Pi.single_eq_same, abs_of_pos hη]
      linarith
    · rw [Pi.single_eq_of_ne h, abs_zero]
      linarith
  intro μ
  fin_cases i
  · simpa [edgeStart] using hη.le
  · simpa [edgeStart] using hs _ μ
  · simpa [edgeStart] using hs _ μ
  · simpa [edgeStart] using hη.le
theorem norm_edgeValues_le (ι : Fin 3 × PeriodicOperators.PosEdge L k 0)
    (p : Face L k 0) (l : Fin 4) :
    ‖edgeValues (basisFunction ι : CoeffField L k) p l‖ ≤ pauliNormSum := by
  classical
  have h : ∀ x, ‖(basisFunction ι : CoeffField L k) x‖ ≤ 1 := fun x => by
    by_cases hx : x = ι
    · rw [show (basisFunction ι : CoeffField L k) x = 1 from if_pos hx]
      simp
    · rw [show (basisFunction ι : CoeffField L k) x = 0 from if_neg hx]
      simp
  have := norm_ofPauliCoeffs_le (basisFunction ι : CoeffField L k) (posEdgeOf p l) (m := 1)
    fun e => h _
  rw [mul_one] at this
  exact this
theorem norm_exponentMap_smul_mesh_le (hη : 0 < finestMesh L k) (p : Face L k 0)
    (l j : Fin 4) (A : CoeffField L k) {M : ℝ} (h : ‖ofPauliCoeffs A (posEdgeOf p j)‖ ≤ M) :
    ‖exponentMap p l j (((finestMesh L k : ℝ) : ℂ) • A)‖ ≤ finestMesh L k * M := by
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hη.le]
  exact mul_le_mul_of_nonneg_left (norm_exponentMap_le p l j A h) hη.le
theorem edgeValues_eq_zero (p : Face L k 0) (c : Fin 3)
    (b : PeriodicOperators.PosEdge L k 0) (hne : ∀ i, posEdgeOf p i ≠ b) :
    edgeValues (basisFunction (c, b) : CoeffField L k) p = 0 := by
  classical
  funext i
  change ∑ e, (basisFunction (c, b) : CoeffField L k) (e, posEdgeOf p i) •
    ComplexMatrix2.pauliFamily e = 0
  refine Finset.sum_eq_zero fun e _ => ?_
  have : (basisFunction (c, b) : CoeffField L k) (e, posEdgeOf p i) = 0 :=
    if_neg fun h => hne i (congrArg Prod.snd h)
  rw [this, zero_smul]
theorem coeffForms_zero (p : Face L k 0) (a : Fin 3) (ζ ζ' : CoeffField L k) :
    firstCoeffForm p a 0 ζ = 0 ∧ secondCoeffForm p a 0 ζ ζ' = 0 := by
  refine ⟨?_, ?_⟩
  · rw [firstCoeffForm_apply]
    simp [bracket]
  · rw [secondCoeffForm_apply]
    simp [secondOrderTerm, bracket]
theorem norm_firstCoeffForm_le (hη : 0 < finestMesh L k) {M : ℝ} (hM : 0 ≤ M)
    (p : Face L k 0) (a : Fin 3) (ι : Fin 3 × PeriodicOperators.PosEdge L k 0)
    (A : CoeffField L k) (hA : ∀ j, ‖ofPauliCoeffs A (posEdgeOf p j)‖ ≤ M) :
    ‖firstCoeffForm p a (edgeValues (basisFunction ι : CoeffField L k) p)
      (((finestMesh L k : ℝ) : ℂ) • A)‖ ≤ 512 * pauliComponentBound * pauliNormSum * M := by
  have hE := pauliComponentBound_nonneg
  have hP := pauliNormSum_nonneg
  rw [firstCoeffForm_apply]
  have hterm : ∀ l, ‖pauliComponentForm a (bracket
      (∑ j, exponentMap p l j (((finestMesh L k : ℝ) : ℂ) • A))
      (edgeValues (basisFunction ι : CoeffField L k) p l))‖ ≤
      pauliComponentBound * (8 * (finestMesh L k * M) * pauliNormSum) := fun l => by
    refine (norm_pauliEntryForm_le a _).trans (mul_le_mul_of_nonneg_left ?_ hE)
    refine (norm_bracket_sum_le_mul
      (fun j => norm_exponentMap_smul_mesh_le hη p l j A (hA j)) _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_edgeValues_le ι p l) (by positivity)
  refine (norm_sum_signedInvMesh_le hη _ hterm).trans ?_
  have e : 4 * ((finestMesh L k)⁻¹ * (pauliComponentBound * (8 * (finestMesh L k * M) *
      pauliNormSum))) = 32 * pauliComponentBound * pauliNormSum * M := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ pauliComponentBound * pauliNormSum * M := by positivity
  nlinarith
theorem norm_secondCoeffForm_le (hη : 0 < finestMesh L k) (hη1 : finestMesh L k ≤ 1) {M : ℝ}
    (hM : 0 ≤ M) (p : Face L k 0) (a : Fin 3)
    (ι : Fin 3 × PeriodicOperators.PosEdge L k 0) (A A' : CoeffField L k)
    (hA : ∀ j, ‖ofPauliCoeffs A (posEdgeOf p j)‖ ≤ M)
    (hA' : ∀ j, ‖ofPauliCoeffs A' (posEdgeOf p j)‖ ≤ M) :
    ‖secondCoeffForm p a (edgeValues (basisFunction ι : CoeffField L k) p)
      (((finestMesh L k : ℝ) : ℂ) • A) (((finestMesh L k : ℝ) : ℂ) • A')‖ ≤
      512 * pauliComponentBound * pauliNormSum * M ^ 2 := by
  have hE := pauliComponentBound_nonneg
  have hP := pauliNormSum_nonneg
  have hηM : 0 ≤ finestMesh L k * M := mul_nonneg hη.le hM
  rw [secondCoeffForm_apply]
  have hterm : ∀ l, ‖pauliComponentForm a (secondOrderTerm
      (fun j => exponentMap p l j (((finestMesh L k : ℝ) : ℂ) • A))
      (fun j => exponentMap p l j (((finestMesh L k : ℝ) : ℂ) • A'))
      (edgeValues (basisFunction ι : CoeffField L k) p l))‖ ≤
      pauliComponentBound * (128 * (finestMesh L k * M) ^ 2 * pauliNormSum) := fun l => by
    refine (norm_pauliEntryForm_le a _).trans (mul_le_mul_of_nonneg_left ?_ hE)
    refine (norm_secondOrderTerm_le hηM
      (fun j => norm_exponentMap_smul_mesh_le hη p l j A (hA j))
      (fun j => norm_exponentMap_smul_mesh_le hη p l j A' (hA' j)) _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_edgeValues_le ι p l) (by positivity)
  refine (norm_sum_signedInvMesh_le hη _ hterm).trans ?_
  have e : 4 * ((finestMesh L k)⁻¹ * (pauliComponentBound * (128 * (finestMesh L k * M) ^ 2 *
      pauliNormSum))) = finestMesh L k * (512 * pauliComponentBound * pauliNormSum * M ^ 2) := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ 512 * pauliComponentBound * pauliNormSum * M ^ 2 := by positivity
  calc _ ≤ 1 * (512 * pauliComponentBound * pauliNormSum * M ^ 2) :=
        mul_le_mul_of_nonneg_right hη1 this
    _ = _ := one_mul _
theorem holonomyDefectCoeffsBounded_holds (hT : ExpansionCoefficients.Claim)
    (hX : ComplexMatrix2.FourExpConjugation.SecondOrderExpansion)
    (hLoc : HolonomyDefectLocality.KernelIsLocal)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hEnt : GaugeFieldOfFormEntries)
    (hI : TowerIndexSets.Claim) : HolonomyDefectCoeffsBounded := by
  classical
  intro L hL
  have hE := pauliComponentBound_nonneg
  have hP := pauliNormSum_nonneg
  refine ⟨512 * pauliComponentBound * pauliNormSum, by positivity, fun k hk => ?_⟩
  have hη : 0 < finestMesh L k := by
    have hL0 : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    exact zpow_pos hL0 _
  have hη1 : finestMesh L k ≤ 1 := by
    have hL1 : (1 : ℝ) ≤ L := by
      have := hL.2
      exact_mod_cast (by omega : 1 ≤ L)
    exact zpow_le_one_of_nonpos₀ hL1 (by simp)
  have hcfg := (hEnt L hL k).1
  obtain ⟨-, hB, hPl⟩ := hI L hL k 0 (Nat.zero_le k)
  have hloc : IsLocalOpFun (remainderIndex L k) (colourEdges L k 0)
      (colourFaces L k 0)
      (fun f => holonomyDefectKernel L k (gaugeFieldOfForm L k f)) :=
    ⟨1, 2 * finestMesh L k, (hLoc L hL k hk).1 1 one_pos⟩
  have hco := fun a p ι ζ ζ' => coeffOne_coeffTwo_eq hη hT hX hK hcfg hB hPl hloc a p ι ζ ζ'
  refine ⟨?_, ?_⟩
  · rintro ζ ζ' ⟨a, p⟩ ⟨c, b⟩ hfar
    have hY := edgeValues_eq_zero p c b fun i h => hfar (by
      have := withinBox_corner hη p i
      rw [h] at this
      exact this)
    obtain ⟨h₁, h₂⟩ := hco a p (c, b) ζ ζ'
    rw [hY] at h₁ h₂
    exact ⟨h₁.trans (coeffForms_zero p a ζ ζ').1, h₂.trans (coeffForms_zero p a ζ ζ').2⟩
  · rintro A A' M ⟨a, p⟩ ι hM hA hA'
    obtain ⟨h₁, h₂⟩ := hco a p ι (((finestMesh L k : ℝ) : ℂ) • A)
      (((finestMesh L k : ℝ) : ℂ) • A')
    have hb : ∀ j, ‖ofPauliCoeffs A (posEdgeOf p j)‖ ≤ M := fun j =>
      hA.1 (posEdgeOf p j) (withinBox_corner hη p j)
    have hb' : ∀ j, ‖ofPauliCoeffs A' (posEdgeOf p j)‖ ≤ M := fun j =>
      hA'.1 (posEdgeOf p j) (withinBox_corner hη p j)
    exact ⟨(congrArg norm h₁).le.trans (norm_firstCoeffForm_le hη hM p a ι A hb),
      (congrArg norm h₂).le.trans (norm_secondCoeffForm_le hη hη1 hM p a ι A A' hb hb')⟩
end YangMills.Construction.Tower.FullSpace.HolonomyDefectCoeffs
end
