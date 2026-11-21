import YangMills.Construction.Torus.AveragingOperatorAndMatricesProof
import YangMills.Construction.Torus.BoundOnTheScaledRemainderBlocks
import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNorms
import YangMills.Construction.Torus.FloorsOfTheAveragedSquareExpansion
import YangMills.Construction.Torus.GeometryOfCovers
import YangMills.Construction.Torus.KernelCalculusOnTheLayers
import YangMills.Construction.Torus.UpperBoundOnThePairScaledMatrix
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace Weighted.RemainderBlockBound
section Numbers
theorem greenDecayRate_pos {L : ℕ} (hL : 0 < L) : 0 < greenDecayRate 4 L := by
  have : (0 : ℝ) < L := by exact_mod_cast hL
  unfold greenDecayRate
  positivity
end Numbers
variable {D : TorusData} (B : SeparatedChain D)
section Matrices
variable {B}
theorem kernel_add (K K' : B.LayerOp) (y y' : ↥B.allSites) :
    B.kernel (K + K') y y' = B.kernel K y y' + B.kernel K' y y' := rfl
theorem kernel_mulOnLayer_mul (g : D.Space → ℝ) (K : B.LayerOp) (y y' : ↥B.allSites) :
    B.kernel ((B.mulOnLayer g : Module.End ℝ B.LayerFn) * K) y y' =
      g y * B.kernel K y y' := rfl
theorem kernel_mul_mulOnLayer (g : D.Space → ℝ) (K : B.LayerOp) (y y' : ↥B.allSites) :
    B.kernel ((K : Module.End ℝ B.LayerFn) * B.mulOnLayer g) y y' =
      B.kernel K y y' * g y' := by
  have h : B.mulOnLayer g (({y'} : Set ↥B.allSites).indicator 1) =
      g y' • (({y'} : Set ↥B.allSites).indicator 1 : B.LayerFn) := by
    funext z
    change g z * _ = g y' * _
    by_cases hz : z = y'
    · rw [hz]
    · simp [indicator, hz]
  change K (B.mulOnLayer g (({y'} : Set ↥B.allSites).indicator 1)) y = _
  rw [h, map_smul]
  change g y' * K _ y = K _ y * g y'
  ring
end Matrices
section Geometry
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem weightedDistance_nonneg (x x' : D.Space) : 0 ≤ B.weightedDistance x x' := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.weightedDistance_nonneg <;> assumption
end Geometry
end Weighted.RemainderBlockBound
end YangMills.Construction
