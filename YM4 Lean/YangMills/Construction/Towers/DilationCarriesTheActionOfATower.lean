import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ScalingPreservesActionAllSides : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    ∀ (j : ℕ) (hj : j ≤ k) (n : ℕ), 0 < n → ScalingPreservesAction hL hj n
end YangMills.Construction.Tower
end
