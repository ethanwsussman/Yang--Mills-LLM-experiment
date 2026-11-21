import YangMills.Construction.Torus.AveragesOfTheExpansionTestFormsProof
import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import YangMills.Construction.Torus.FunctionsOfTheSupDistanceAndTheWeightedDistanceProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace WeightedLengthBounds
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem norm_le_torusL1Norm {S : ℝ} (x : Torus4 S) : ‖x‖ ≤ torusL1Norm x := by apply _root_.YangMills.Construction.Weighted.LocalLip.norm_le_torusL1Norm <;> assumption
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_mono (D : ScaleData) {i m : ℕ} (h : i ≤ m) :
    D.levelSpacing i ≤ D.levelSpacing m := by apply _root_.YangMills.Construction.GeneralTorus.SupDistBound.levelSpacing_mono <;> assumption
theorem pathLengthIn_nonneg (S : ℝ) (Γ : List LiftedSegment) (A : Set (Torus4 S)) :
    0 ≤ pathLengthIn S Γ A := by apply _root_.YangMills.Construction.Weighted.DistBounds.pathLengthIn_nonneg <;> assumption
theorem measurableSet_segmentsSupport (S : ℝ) (Γ : List LiftedSegment) :
    MeasurableSet (segmentsSupport S Γ) := by
  have hc : IsCompact (segmentsSupport S Γ) := by
    refine Set.Finite.isCompact_biUnion (s := {s | s ∈ Γ}) Γ.finite_toSet fun s _ => ?_
    refine isCompact_Icc.image (continuous_pi fun μ => ?_)
    refine (AddCircle.continuous_mk' S).comp ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  exact hc.isClosed.measurableSet
variable {D : ScaleData} (B : SeparatedChain D)
end WeightedLengthBounds
end YangMills.Construction.GeneralTorus
end
