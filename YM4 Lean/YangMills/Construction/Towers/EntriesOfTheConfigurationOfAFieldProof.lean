import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import YangMills.Construction.Towers.AverageIsDifferentiableOnThePolydiscProof
import YangMills.Construction.Towers.EntriesOfTheConfigurationOfAField
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
namespace FieldOfFormEntries
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.EntireDependence
open YangMills.Construction.Tower.FullSpace.BackgroundJets (gaugeFieldOfForm)
private theorem meshAt_ne_zero {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    meshAt L k 0 ≠ 0 := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.finestMesh_ne_zero <;> assumption
private theorem opposite_not_positive {a : ℝ} (ha : a ≠ 0) {e : InfiniteLattice.Link a}
    (h : e.IsPositivelyOriented) : ¬e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
private theorem opposite_positive_of_not {a : ℝ} {e : InfiniteLattice.Link a}
    (h : ¬e.IsPositivelyOriented) : e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
private theorem evaluation_of_positive {L k : ℕ} (ζ : (remainderIndex L k).Carrier → ℂ)
    {e : Edge L k 0} (h : e.IsPositivelyOriented) :
    (edgePauliCoordinates L k 0).ofCoeffs ζ e = ofPauliCoeffs ζ ⟨e, h⟩ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_of_pos <;> assumption
private theorem trace_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) (e : σ) :
    Matrix.trace (ofPauliCoeffs c e) = 0 := by
  simp only [ofPauliCoeffs, Matrices.ComplexMatrix2.sum_smul_pauliFamily, Matrix.trace_fin_two]
  simp
private theorem trace_coordinates_eq_zero {L k : ℕ} (ζ : (remainderIndex L k).Carrier → ℂ)
    (e : Edge L k 0) : Matrix.trace ((edgePauliCoordinates L k 0).ofCoeffs ζ e) = 0 := by
  classical
  by_cases h : e.IsPositivelyOriented
  · rw [evaluation_of_positive ζ h]
    exact trace_ofPauliCoeffs _ _
  · have hr := opposite_positive_of_not h
    have : (edgePauliCoordinates L k 0).ofCoeffs ζ e = -ofPauliCoeffs ζ ⟨e.opposite, hr⟩ := by
      simp [edgePauliCoordinates, extendOddly, h, hr]
    rw [this, Matrix.trace_neg]
    exact neg_eq_zero.mpr (trace_ofPauliCoeffs _ _)
private theorem field_of_positive {L k : ℕ} (ζ : (remainderIndex L k).Carrier → ℂ)
    {e : Edge L k 0} (h : e.IsPositivelyOriented) :
    gaugeFieldOfForm L k ζ e =
      Matrices.ComplexMatrix2.matExp (Complex.I • ofPauliCoeffs ζ ⟨e, h⟩) := by
  simp [gaugeFieldOfForm, expForm, expTwist, h, evaluation_of_positive ζ h]
private theorem field_of_not_positive {L k : ℕ} (ζ : (remainderIndex L k).Carrier → ℂ)
    {e : Edge L k 0} (h : ¬e.IsPositivelyOriented) :
    gaugeFieldOfForm L k ζ e =
      (Matrices.ComplexMatrix2.matExp
        (Complex.I • (edgePauliCoordinates L k 0).ofCoeffs ζ e.opposite))⁻¹ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.gaugeFieldOfForm_of_not_pos <;> assumption
private theorem det_matExp_I {X : Matrices.ComplexMatrix2} (h : Matrix.trace X = 0) :
    (Matrices.ComplexMatrix2.matExp (Complex.I • X)).det = 1 :=
  SpinHarmonics.det_matExp_of_trace_eq_zero (by
    simp [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_smul, h])
private theorem matExp_inv (Z : Matrices.ComplexMatrix2) :
    (Matrices.ComplexMatrix2.matExp Z)⁻¹ = Matrices.ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem field_mem {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ)
    (ζ : (remainderIndex L k).Carrier → ℂ) :
    gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · change Matrix.det _ = 1
    by_cases h : e.IsPositivelyOriented
    · rw [field_of_positive ζ h]
      exact det_matExp_I (trace_ofPauliCoeffs _ _)
    · rw [field_of_not_positive ζ h, Matrix.det_nonsing_inv, det_matExp_I (trace_coordinates_eq_zero ζ _)]
      simp
  · by_cases h : e.IsPositivelyOriented
    · have hr := opposite_not_positive (meshAt_ne_zero hL k) h
      rw [field_of_not_positive ζ hr, field_of_positive ζ h]
      change (Matrices.ComplexMatrix2.matExp
        (Complex.I • (edgePauliCoordinates L k 0).ofCoeffs ζ e))⁻¹ = _
      rw [evaluation_of_positive ζ h]
    · have hr := opposite_positive_of_not h
      rw [field_of_positive ζ hr, field_of_not_positive ζ h, evaluation_of_positive ζ hr,
        matExp_inv, matExp_inv, neg_neg]
private theorem mem_edgeIndices {L k : ℕ} (a : Fin 3) (e : PeriodicOperators.PosEdge L k 0) :
    (show (remainderIndex L k).Carrier from (a, e)) ∈ edgeIndices L k e :=
  @Finset.mem_image_of_mem _ _ (fun _ _ => Classical.propDecidable _) _ _ _ (Finset.mem_univ a)
private def pauliSumOn {L k : ℕ} (e : PeriodicOperators.PosEdge L k 0)
    (w : ↥(edgeIndices L k e) → ℂ) : Matrices.ComplexMatrix2 :=
  ∑ a, w ⟨(a, e), mem_edgeIndices a e⟩ • Matrices.ComplexMatrix2.pauliFamily a
private theorem differentiable_pauliSumOn {L k : ℕ} (e : PeriodicOperators.PosEdge L k 0) :
    Differentiable ℂ (pauliSumOn e) := by
  unfold pauliSumOn
  exact Differentiable.fun_sum fun a _ => (differentiable_apply _).smul_const _
private theorem isEntireOn_matExp {L k : ℕ} (e : PeriodicOperators.PosEdge L k 0) (i j : Fin 2)
    (s : ℂ) :
    IsEntireOn (remainderIndex L k) (edgeIndices L k e)
      (fun ζ => Matrices.ComplexMatrix2.matExp (s • ofPauliCoeffs ζ e) i j) := by
  refine ⟨fun w => Matrices.ComplexMatrix2.matExp (s • pauliSumOn e w) i j, ?_, fun ζ => rfl⟩
  have hexp : Differentiable ℂ Matrices.ComplexMatrix2.matExp := fun x =>
    (NormedSpace.exp_analytic (𝕂 := ℂ) x).differentiableAt
  have hin : Differentiable ℂ fun w => Matrices.ComplexMatrix2.matExp (s • pauliSumOn e w) :=
    hexp.comp ((differentiable_pauliSumOn e).const_smul s)
  exact ((Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap.differentiable).comp hin
end FieldOfFormEntries
open FieldOfFormEntries in
theorem gaugeFieldOfFormEntries_holds : GaugeFieldOfFormEntries := by
  intro L hL k
  refine ⟨field_mem hL k, fun e i j => ⟨?_, ?_⟩⟩
  · have h := isEntireOn_matExp (L := L) (k := k) e i j Complex.I
    convert h using 2 with ζ
    rw [field_of_positive ζ e.2]
  · have h := isEntireOn_matExp (L := L) (k := k) e i j (-Complex.I)
    convert h using 2 with ζ
    rw [field_of_positive ζ e.2, matExp_inv, neg_smul]
end YangMills.Construction.Tower.FullSpace
end
