import YangMills.Construction.Torus.FunctionsOfTheSupDistanceAndTheWeightedDistanceProof
import YangMills.Construction.Torus.PartsOfTheGeometryOfCubes
import YangMills.Construction.Torus.WeightedDistanceAndCellsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace CubeDistanceBounds
variable {D : ScaleData}
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_mono (D : ScaleData) {m n : ℕ} (h : m ≤ n) :
    D.levelSpacing m ≤ D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.SupDistBound.levelSpacing_mono <;> assumption
end CubeDistanceBounds
end YangMills.Construction.GeneralTorus
end
