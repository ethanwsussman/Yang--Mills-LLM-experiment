import YangMills.Construction.WeightedGreen.DecayRateDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Dirichlet
def localFormConst (L : ℕ) (aLow : ℝ) : ℝ :=
  24 * Real.exp (7 / 3) * (L : ℝ) ^ 2 * (YangMills.Construction.WeightedGreen.coercivityConst aLow)⁻¹
end YangMills.Construction.Dirichlet
