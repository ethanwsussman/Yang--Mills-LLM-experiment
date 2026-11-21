import YangMills.Construction.Torus.BoundsOnTheInversesOfTheCubes
import YangMills.Construction.Torus.PartsOfTheGeometryOfCubes
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus.ApproxInverseTerms
variable (C : CubeGaugeSetting)
theorem coarseSpacing_pos (b : C.CoarseBond) : 0 < GaugeSetting.coarseSpacing b := by
  have hL : (0 : ℝ) < C.data.L := by
    have := C.data.blocking.thirteen_le
    have h : 0 < C.data.L := by omega
    exact_mod_cast h
  have := C.data.baseSpacing_pos
  unfold GaugeSetting.coarseSpacing ScaleData.levelSpacing
  positivity
end YangMills.Construction.GeneralTorus.ApproxInverseTerms
end
