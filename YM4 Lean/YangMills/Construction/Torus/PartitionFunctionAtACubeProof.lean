import YangMills.Construction.Torus.CubeSetsBumpsCutOffsAndProductRule
import YangMills.Construction.Torus.PartsOfTheGeometryOfCubes
import YangMills.Construction.Torus.WeightedDistanceAndCellsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus.UnityWeight
variable (C : CubeGaugeSetting)
theorem L_pos : (0 : ℝ) < C.data.L := by
  have := C.data.blocking.thirteen_le
  have h : 0 < C.data.L := by omega
  exact_mod_cast h
theorem blockCount_pos : (0 : ℝ) < C.data.blockCount := by
  have h1 := C.twelve_mul_L_le_blockCount
  have h2 := C.data.blocking.thirteen_le
  have h : 0 < C.data.blockCount := by omega
  exact_mod_cast h
theorem L_le_blockCount : C.data.L ≤ C.data.blockCount := by
  have h1 := C.twelve_mul_L_le_blockCount
  omega
theorem levelSpacing_pos (n : ℕ) : 0 < C.data.levelSpacing n := by
  have := L_pos C
  have := C.data.baseSpacing_pos
  unfold ScaleData.levelSpacing
  positivity
end GeneralTorus.UnityWeight
end YangMills.Construction
