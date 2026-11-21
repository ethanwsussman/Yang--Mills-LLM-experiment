import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def ScalingPreservesObjectsAtLevel.Statement : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    ∀ (j : ℕ) (hj : j ≤ k), 1 ≤ j → ∀ i ≤ j,
      (∀ n : ℕ, 0 < n → ScalingPreservesAtLevel hL hj n i) ∧
        FullSpace.PreservesAtLevel hL hj i
end Tower
end YangMills.Construction
end
