import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.TrivialLinearization
def OneStepIdentitiesHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    OneStepIdentities L k j
end YangMills.Construction.Tower.FullSpace.TrivialLinearization
end
