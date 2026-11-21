import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    Tower.RescaledConditions.BackgroundFormMatchesHessian L n k
end YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide
end
