import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LinearizationFacts
def pivotFormsStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ n k j : ℕ, 0 < n → j < k →
      YangMills.Construction.Tower.TrivialLinearization.OneStepPivotSupported L n k j
end YangMills.Construction.Tower.LinearizationFacts
end
