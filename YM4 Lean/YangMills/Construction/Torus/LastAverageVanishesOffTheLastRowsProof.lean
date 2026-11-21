import YangMills.Construction.Torus.ClosedFormsWithVanishingAveragesAreGradientsProof
import YangMills.Construction.Geometry.UnitLatticeBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus
namespace TopLevelMean
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
variable {D : ScaleData}
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_succ (k : ℕ) : D.levelSpacing (k + 1) = (D.L : ℝ) * D.levelSpacing k := by apply _root_.YangMills.Construction.GeneralTorus.ClosedMeanFree.levelSpacing_succ <;> assumption
end TopLevelMean
end GeneralTorus
end YangMills.Construction
