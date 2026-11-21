import YangMills.Construction.Torus.PropertiesOfTheWeightedDistanceAndCells
import YangMills.Construction.Torus.LayersCellsBlocksAndTheDistanceProof
import YangMills.Construction.Weighted.LocalLipCalculusProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MeasureTheory TorusMetric
open scoped ENNReal
namespace GeneralTorus
namespace SupDistBound
variable {S : ℝ}
theorem torusSupNorm_eq_norm (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem norm_le_torusL1Norm (x : Torus4 S) : ‖x‖ ≤ torusL1Norm x := by apply _root_.YangMills.Construction.Weighted.LocalLip.norm_le_torusL1Norm <;> assumption
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_mono (D : ScaleData) {m n : ℕ} (h : m ≤ n) :
    D.levelSpacing m ≤ D.levelSpacing n := by
  have hL : 1 ≤ D.L := by
    have := D.blocking.thirteen_le
    omega
  have hL' : (1 : ℝ) ≤ D.L := by exact_mod_cast hL
  unfold ScaleData.levelSpacing
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL' h) D.baseSpacing_pos.le
variable {D : ScaleData}
theorem isClosed_segmentsSupport (D : ScaleData) (Γ : List LiftedSegment) :
    IsClosed (segmentsSupport D.torusSide Γ) := by
  unfold segmentsSupport
  refine Set.Finite.isClosed_biUnion (List.finite_toSet Γ) fun s _ => ?_
  refine (isCompact_Icc.image ?_).isClosed
  refine continuous_pi fun μ => ?_
  have h : Continuous fun t : ℝ => (t : AddCircle D.torusSide) := continuous_quotient_mk'
  exact h.comp (by fun_prop)
end SupDistBound
end GeneralTorus
end YangMills.Construction
end
