import YangMills.Construction.SeparatedSequences.RestrictionOfBackgroundsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
open BackgroundRestriction
def coreGaugeLowerBound (L : ℕ) (B₃ : ℝ) : ℝ := 2 * holonomyBound L * B₃
end YangMills.Construction.ParameterChoice
end
