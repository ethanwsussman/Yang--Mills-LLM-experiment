import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.LinearizationFacts
def constantFormsStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    YangMills.Construction.Tower.FullSpace.TrivialLinearization.OneStepConstantForms L k j
end YangMills.Construction.Tower.FullSpace.LinearizationFacts
end
