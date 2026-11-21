import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ResponseBoundExists : Prop := ∃ C : ℝ, ResponseProperties.ResponseBound C
end YangMills.Construction.Tower
end
