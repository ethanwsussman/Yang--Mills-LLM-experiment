import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower.RescaledConditions
def Holds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ, 0 < n → OnTorus L n k ∧ BackgroundFormMatchesHessian L n k) ∧
    Tower.FullSpace.RescaledConditions.OnFullSpace L k
end Tower.RescaledConditions
end YangMills.Construction
end
