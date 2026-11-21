import YangMills.Construction.TwoPoints.RealAnalyticKernelOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TwoPoints
open InfiniteLattice (AmbientSpace)
def formKernel (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : AmbientSpace → ℝ :=
  analyticKernel S
end TwoPoints
end YangMills.Construction
end
