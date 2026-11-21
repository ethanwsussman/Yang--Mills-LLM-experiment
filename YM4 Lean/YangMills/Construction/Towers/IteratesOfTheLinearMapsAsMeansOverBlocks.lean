import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def IteratesAsCubeAverages : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k m : ℕ, 0 < n → m ≤ k →
    TrivialLinearization.IterateAverages L n k m
end YangMills.Construction.Tower
end
