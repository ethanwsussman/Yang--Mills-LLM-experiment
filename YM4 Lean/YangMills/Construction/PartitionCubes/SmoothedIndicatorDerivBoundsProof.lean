import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.PartitionCubes.SmoothedIndicatorDerivatives
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.PartitionCubes
namespace SmoothedIndicatorBounds
theorem contDiff_fderiv_apply {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (e : Fin 4 → ℝ) :
    ContDiff ℝ ∞ fun y => fderiv ℝ f y e :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem mollifierScaled_eq (r : ℝ) :
    mollifierScaled r = fun v => (r ^ 4)⁻¹ * mollifierBump (r⁻¹ • v) := rfl
theorem integral_inv_pow_mul_comp_inv_smul (g : (Fin 4 → ℝ) → ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ t, (r ^ 4)⁻¹ * g (r⁻¹ • t) = ∫ u, g u := by
  rw [integral_const_mul, Measure.integral_comp_smul volume g r⁻¹]
  have hf : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp
  rw [hf, smul_eq_mul, ← mul_assoc]
  have h4 : 0 < r ^ 4 := by positivity
  have : |((r⁻¹) ^ 4)⁻¹| = r ^ 4 := by
    rw [inv_pow, inv_inv, abs_of_pos h4]
  rw [this, inv_mul_cancel₀ h4.ne', one_mul]
theorem integral_mollifierScaled {r : ℝ} (hr : 0 < r) : ∫ v, mollifierScaled r v = 1 := by
  rw [mollifierScaled_eq]
  simp only []
  rw [integral_inv_pow_mul_comp_inv_smul mollifierBump hr, mollifierBump_spec.integral_eq_one]
theorem torusProj_sub (S : ℝ) (p v : Fin 4 → ℝ) :
    Torus.torusProj 4 S p - Torus.torusProj 4 S v = Torus.torusProj 4 S (p - v) := by apply _root_.YangMills.DeltaSharedProofs.p500829 <;> assumption
theorem continuous_torusProj (S : ℝ) : Continuous (Torus.torusProj 4 S) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
variable {𝒮 : RegionSequence.NestedRegions}
end SmoothedIndicatorBounds
end YangMills.Construction.PartitionCubes
end
