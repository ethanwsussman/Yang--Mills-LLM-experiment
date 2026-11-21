import YangMills.Construction.LimitsOfLatticeFamilies.LengthOfAPointGivesAnInvariantDistance
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctionsProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeLimits.InvariantDistFromNorm
open YangMills.Construction.LatticeLimits.ModelSpace YangMills.Construction.TorusMetric
theorem euclidNormVec_eq_norm_toLp (v : Fin 4 → ℝ) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidNormVec_eq_zero_iff {v : Fin 4 → ℝ} : euclidNormVec v = 0 ↔ v = 0 := by
  rw [euclidNormVec_eq_norm_toLp, norm_eq_zero]
  simp
variable {S : ℝ}
theorem torusEuclidNorm_eq_euclidNormVec (x : Torus4 S) :
    torusEuclidNorm x = euclidNormVec fun μ => ‖x μ‖ := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace.torusEuclidNorm_eq_euclidNormVec_norm <;> assumption
theorem torusEuclidNorm_add_le (z z' : Torus4 S) :
    torusEuclidNorm (z + z') ≤ torusEuclidNorm z + torusEuclidNorm z' := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
theorem torusEuclidNorm_neg (z : Torus4 S) : torusEuclidNorm (-z) = torusEuclidNorm z := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.torusEuclidNorm_neg <;> assumption
theorem torusEuclidNorm_nonneg (z : Torus4 S) : 0 ≤ torusEuclidNorm z := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
theorem torusEuclidNorm_eq_zero_iff {z : Torus4 S} : torusEuclidNorm z = 0 ↔ z = 0 := by
  rw [torusEuclidNorm_eq_euclidNormVec, euclidNormVec_eq_zero_iff]
  simp [funext_iff]
theorem norm_properties (s : Conventions.StandingParameters) (Y : ModelSpace) :
    (∀ z z' : Y.Carrier s, ModelSpace.norm s Y (z + z') ≤ ModelSpace.norm s Y z + ModelSpace.norm s Y z') ∧
    (∀ z : Y.Carrier s, ModelSpace.norm s Y (-z) = ModelSpace.norm s Y z) ∧
    (∀ z : Y.Carrier s, 0 ≤ ModelSpace.norm s Y z) ∧
    ∀ z : Y.Carrier s, ModelSpace.norm s Y z = 0 ↔ z = 0 := by
  cases Y with
  | euclidean =>
    exact ⟨euclidNormVec_add_le, euclidNormVec_neg, fun _ => Real.sqrt_nonneg _,
      fun _ => euclidNormVec_eq_zero_iff⟩
  | torus =>
    exact ⟨torusEuclidNorm_add_le, torusEuclidNorm_neg, torusEuclidNorm_nonneg,
      fun _ => torusEuclidNorm_eq_zero_iff⟩
theorem claim_holds : Claim := by
  intro s Y
  obtain ⟨hadd, hneg, hnonneg, hzero⟩ := norm_properties s Y
  refine ⟨hadd, hneg, fun x y => hnonneg _, fun x y => ?_, fun x y => ?_, fun x y w => ?_,
    fun x y a => ?_⟩
  · exact (hzero _).trans sub_eq_zero
  · change ModelSpace.norm s Y (x - y) = ModelSpace.norm s Y (y - x)
    rw [← neg_sub, hneg]
  · change ModelSpace.norm s Y (x - y) ≤ ModelSpace.norm s Y (x - w) + ModelSpace.norm s Y (w - y)
    rw [← sub_add_sub_cancel x w y]
    exact hadd _ _
  · change ModelSpace.norm s Y (x + a - (y + a)) = ModelSpace.norm s Y (x - y)
    rw [add_sub_add_right_eq_sub]
end YangMills.Construction.LatticeLimits.InvariantDistFromNorm
end
