import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def IterateIdentitiesStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ k m : ℕ, m ≤ k → FullSpace.TrivialLinearization.IterateIdentitiesAndBounds L k m
end YangMills.Construction.Tower.FullSpace
end
