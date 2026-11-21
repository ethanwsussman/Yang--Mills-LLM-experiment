import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsOfTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoLevelMixtures
def levelExpansionsAtSmallRateStatement : Prop :=
  ColdStepAtMirrorFrames.EventuallyOrdered fun T => ∀ [NeZero T.L], ∃ r : ℝ, 0 < r ∧ r ≤ T.chainParams.κ₂ ∧ LevelExpansionsBounded T r
end YangMills.Construction.TwoLevelMixtures
end
