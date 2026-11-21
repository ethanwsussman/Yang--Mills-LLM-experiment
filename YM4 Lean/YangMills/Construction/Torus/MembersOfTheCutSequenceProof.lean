import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Torus.AveragesOfTheExpansionTestFormsProof
import YangMills.Construction.Torus.PartsOfTheGeometryOfCubes
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric
open scoped ENNReal
noncomputable section
namespace GeneralTorus
namespace CutChainLocal
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem continuous_torusSupNorm {S : ℝ} : Continuous (torusSupNorm : Torus4 S → ℝ) := by
  have : (torusSupNorm : Torus4 S → ℝ) = fun x => ‖x‖ := funext torusSupNorm_eq_norm
  rw [this]
  exact continuous_norm
variable (D : ScaleData)
theorem blockCount_pos : 0 < D.blockCount := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.blockCount_pos <;> assumption
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
variable {D}
namespace Chain
variable (B : SeparatedChain D) (Q : D.CubeIndex)
theorem set_antitone {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.lastLevel) : B.set j ⊆ B.set i := by apply _root_.YangMills.Construction.GeneralTorus.CoarseTestFormMeansAux.set_antitone <;> assumption
end Chain
end CutChainLocal
end GeneralTorus
end
end YangMills.Construction
