import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace TrivialLinearization
def AllRelationsStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ n k j m : ℕ, 0 < n → j < k → m ≤ k →
      OneStepIdentities L n k j ∧ OneStepConstantForms L n k j ∧ OneStepPivotSupported L n k j ∧
        SmoothingsSurjective L n k j m ∧ IterateIdentitiesAndBounds L n k m ∧
        IterateAverages L n k m) ∧
    ∀ k j m : ℕ, j < k → m ≤ k →
      FullSpace.TrivialLinearization.OneStepIdentities L k j ∧
        FullSpace.TrivialLinearization.OneStepConstantForms L k j ∧
        FullSpace.TrivialLinearization.OneStepPivotSupported L k j ∧
        FullSpace.TrivialLinearization.SmoothingsSurjective L k j m ∧
        FullSpace.TrivialLinearization.IterateIdentitiesAndBounds L k m ∧
        FullSpace.TrivialLinearization.IterateAverages L k m
end TrivialLinearization
end Tower
end YangMills.Construction
end
