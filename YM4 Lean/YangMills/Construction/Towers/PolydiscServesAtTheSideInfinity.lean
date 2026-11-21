import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
def PolydiscIsAdmissibleAtInfiniteSide : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ ρ : ℝ, 0 < ρ →
    (∀ k j : ℕ, j < k → ∀ c : Edge L 1 k (j + 1), c.IsPositivelyOriented →
      PolydiscIsAdmissible ρ c) →
    ∀ k j : ℕ, j < k → ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      FullSpace.PolydiscIsAdmissible L k j ρ c
end YangMills.Construction.Tower
