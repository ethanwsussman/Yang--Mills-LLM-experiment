import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def FullSpace.ProjPreservesFieldsEverywhere : Prop :=
  ∀ (L : ℕ) (_hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    1 ≤ k → ∀ n : ℕ, 0 < n → ∀ i < k, ∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
      FullSpace.ProjPreservesFields L n k i c
end YangMills.Construction.Tower
end
