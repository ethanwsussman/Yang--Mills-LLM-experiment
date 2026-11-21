import YangMills.Construction.RegionSequence.WeightedDistTriangleProof
import YangMills.Construction.Dirichlet.ShellCrossingChainsOfPaths
import YangMills.Construction.DirichletOperator.AveragingOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.Torus.TorusLengthsProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.WeightedDistBall
variable {d : ℕ} {S : ℝ}
theorem norm_torusProj_le (v : Fin d → ℝ) : ‖torusProj d S v‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ =>
    (TorusMetric.addCircle_norm_coe_le_abs (v μ)).trans (by simpa using norm_le_pi_norm v μ)
theorem supNorm_eq_norm (p : PeriodicTorus d S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.Torus.supNorm_eq_norm <;> assumption
theorem lOneLength_nonneg (σ : TorusSegment d) : 0 ≤ σ.lOneLength :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem pointAt_sub_pointAt (σ : TorusSegment d) (t t' : ℝ) :
    σ.pointAt S t - σ.pointAt S t' = torusProj d S ((t - t') • σ.direction) := by
  funext μ
  simp only [TorusSegment.pointAt, torusProj, Pi.sub_apply]
  rw [← AddCircle.coe_sub]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem lengthWithin_nonneg (Γ : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) :
    0 ≤ lengthWithin Γ X := by apply _root_.YangMills.Construction.Dirichlet.Crossing.lengthWithin_nonneg <;> assumption
theorem scale_pos (R : NestedRegions) (n : ℕ) : 0 < R.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_mono (R : NestedRegions) {k j : ℕ} (h : k ≤ j) : R.scale k ≤ R.scale j := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.scale_mono <;> assumption
theorem scale_zero (R : NestedRegions) : R.scale 0 = R.ξ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.scale_zero <;> assumption
end YangMills.Construction.WeightedDistBall
end
