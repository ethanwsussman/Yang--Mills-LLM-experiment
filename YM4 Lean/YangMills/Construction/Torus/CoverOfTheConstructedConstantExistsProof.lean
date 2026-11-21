import YangMills.Construction.Torus.ComparisonOfLocalScaledSquaresProof
import YangMills.Construction.Torus.StandardPartitionsLayersBlocksAndBallsProof
import YangMills.Construction.Weighted.LocalLipCalculus
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace Weighted
namespace CoverConstruction
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
variable {D : TorusData}
theorem cast_L_pos (D : TorusData) : (0 : ℝ) < D.L := by apply _root_.YangMills.Construction.Weighted.DistanceAvgPairMatrixNormProof.L_pos_real <;> assumption
theorem three_le_cast_L (D : TorusData) : (3 : ℝ) ≤ D.L := by apply _root_.YangMills.Construction.Weighted.LocalComparison.three_le_L <;> assumption
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem scale_succ (D : TorusData) (n : ℕ) : D.scale (n + 1) = (D.L : ℝ) * D.scale n := by apply _root_.YangMills.Construction.Weighted.DistBounds.scale_succ <;> assumption
theorem scale_mono (D : TorusData) {a b : ℕ} (h : a ≤ b) : D.scale a ≤ D.scale b := by apply _root_.YangMills.Construction.Weighted.DistBounds.scale_mono <;> assumption
theorem blockSide_pos (D : TorusData) (j : ℕ) : 0 < D.blockSide j := by apply _root_.YangMills.Construction.Weighted.LocalComparison.blockSide_pos <;> assumption
theorem blockSide_eq_scale (D : TorusData) {m : ℕ} (hm : D.blockNumber = D.L ^ m) (j : ℕ) :
    D.blockSide j = D.scale (j + m) := by apply _root_.YangMills.Construction.Weighted.CubeGeometry.Scales.blockSide_eq_scale <;> assumption
theorem stage_antitone (B : SeparatedChain D) {a b : ℕ} (h : a ≤ b) :
    B.stage b ⊆ B.stage a := by apply _root_.YangMills.Construction.Weighted.DistBounds.stage_anti <;> assumption
end CoverConstruction
end Weighted
end YangMills.Construction
