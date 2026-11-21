import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.LinearizationFacts
def surjectivityStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j m : ℕ, j < k → m ≤ k →
    YangMills.Construction.Tower.FullSpace.TrivialLinearization.SmoothingsSurjective L k j m
end YangMills.Construction.Tower.FullSpace.LinearizationFacts
end
