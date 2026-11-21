import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.ObjectsUnderTheDilation
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace Tower
def ScalingPreservesStepsAtSide.Statement : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    ∀ (j : ℕ) (hj : j ≤ k), 1 ≤ j → ∀ i < j, ∀ n : ℕ, 0 < n → ScalingPreservesAtStep hL hj n i
end Tower
end YangMills.Construction
end
