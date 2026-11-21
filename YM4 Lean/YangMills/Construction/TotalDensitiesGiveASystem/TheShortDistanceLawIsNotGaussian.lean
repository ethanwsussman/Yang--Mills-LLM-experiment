import YangMills.Construction.TotalDensitiesGiveASystem.LawsOfTheTopStatement
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensities.ShortDistanceNonGaussianAtEveryShape
def Statement : Prop := ∀ ϑ ∈ Ioc (0 : ℝ) 1, ShortDistanceLimitNonGaussian ϑ
end YangMills.Construction.TotalDensities.ShortDistanceNonGaussianAtEveryShape
end
