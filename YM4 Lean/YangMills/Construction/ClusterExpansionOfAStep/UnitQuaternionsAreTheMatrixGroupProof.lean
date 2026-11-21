import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAreTheMatrixGroup
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages SoftAverages Matrices TorusFields
namespace UnitQuaternionMatrices
private theorem measurable_equiv :
    Measurable (unitQuaternionEquivSpecialUnitary : UnitQuaternion → ComplexMatrix2.specialUnitary) :=
  (map_continuous unitQuaternionEquivSpecialUnitary).measurable
private theorem map_haarUnit : haarUnit.map unitQuaternionEquivSpecialUnitary = ComplexMatrix2.haarProb := by
  have hp : IsProbabilityMeasure (haarUnit.map unitQuaternionEquivSpecialUnitary) :=
    Measure.isProbabilityMeasure_map measurable_equiv.aemeasurable
  have : (haarUnit.map unitQuaternionEquivSpecialUnitary).IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map haarUnit unitQuaternionEquivSpecialUnitary
  have h := haarMeasure_unique (haarUnit.map unitQuaternionEquivSpecialUnitary)
    (⊤ : TopologicalSpace.PositiveCompacts ComplexMatrix2.specialUnitary)
  have h1 : (haarUnit.map unitQuaternionEquivSpecialUnitary)
      ((⊤ : TopologicalSpace.PositiveCompacts ComplexMatrix2.specialUnitary) :
        Set ComplexMatrix2.specialUnitary) = 1 := by simp
  rw [h1, one_smul] at h
  exact h
private theorem fullTrace_quaternionToMatrix (q : ℍ[ℝ]) :
    ComplexMatrix2.fullTrace (quaternionToMatrix q) = ((2 * q.re : ℝ) : ℂ) := by
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, quaternionToMatrix_apply]
  simp
  ring
private theorem star_mul_quaternionToMatrix (q : ℍ[ℝ]) :
    star (quaternionToMatrix q) * quaternionToMatrix q =
      ((Quaternion.normSq q : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
  rw [← quaternionToMatrix_star, ← quaternionToMatrix_mul, Quaternion.star_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionToMatrix]
private theorem operatorNorm_quaternionToMatrix (q : ℍ[ℝ]) :
    ComplexMatrix2.operatorNorm (quaternionToMatrix q) = ‖q‖ := by
  have h := CStarRing.norm_star_mul_self (x := quaternionToMatrix q)
  rw [star_mul_quaternionToMatrix, norm_smul, norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Quaternion.normSq_nonneg), Quaternion.normSq_eq_norm_mul_self] at h
  exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp h.symm
end UnitQuaternionMatrices
open UnitQuaternionMatrices in
theorem unitQuaternionHaarTraceNorm_holds : UnitQuaternionHaarTraceNorm := by
  refine ⟨map_haarUnit, fun v => ?_, operatorNorm_quaternionToMatrix⟩
  rw [coe_unitQuaternionEquivSpecialUnitary, fullTrace_quaternionToMatrix]
  constructor
  · simp
  · exact Complex.ofReal_im _
end YangMills.Construction.ClusterExpansionOfAStep
end
