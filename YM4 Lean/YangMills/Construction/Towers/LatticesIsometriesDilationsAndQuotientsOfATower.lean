import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower.SublatticesSymmetriesScalingsAndProjections
def Statement : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    Tower.TowerPairs hL k ∧
    Tower.FullSpace.SublatticesNested L k ∧
    (∀ n : ℕ, 0 < n → Tower.SublatticeCounts L n k) ∧
    (∀ n : ℕ, 0 < n → Tower.TorusSymmetries L n k) ∧
    Tower.FullSpace.SpaceSymmetries L k ∧
    (∀ (j : ℕ) (hj : j ≤ k),
      (∀ n : ℕ, 0 < n → Tower.ScalingPreservesTower hL hj n) ∧
        Tower.FullSpace.ScalingPreservesTower hL hj) ∧
    (1 ≤ k → ∀ n : ℕ, 0 < n → Tower.FullSpace.ProjOfTower L n k)
end Tower.SublatticesSymmetriesScalingsAndProjections
end YangMills.Construction
end
