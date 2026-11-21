import YangMills.Construction.EuclideanFunctionals.GapWidthAndFractions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
theorem quarter_pos_of_mem_gapWidthRange {η : ℝ} (hη : η ∈ gapWidthRange) : 0 < η / 4 :=
  div_pos (Set.mem_Ioc.mp hη).1 (by norm_num)
end YangMills.Construction.EuclideanFunctionals
