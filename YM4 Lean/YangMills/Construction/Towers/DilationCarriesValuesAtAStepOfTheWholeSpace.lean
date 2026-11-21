import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def FullSpaceScalingPreservesValues : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    ∀ (j : ℕ) (hj : j ≤ k), 1 ≤ j → ∀ i < j, FullSpace.PreservesValuesAtStep hL hj i
end Tower
end YangMills.Construction
end
