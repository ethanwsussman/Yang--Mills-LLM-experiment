import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LinearizationFacts
def surjectivityStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ n k j m : ℕ, 0 < n → j < k → m ≤ k →
      YangMills.Construction.Tower.TrivialLinearization.SmoothingsSurjective L n k j m
end YangMills.Construction.Tower.LinearizationFacts
end
