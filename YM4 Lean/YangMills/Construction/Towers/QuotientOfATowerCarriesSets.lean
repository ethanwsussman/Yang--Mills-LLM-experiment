import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ProjectionCarriesSetsStatement : Prop :=
  ∀ (L : ℕ) (_hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    1 ≤ k → ∀ n : ℕ, 0 < n → FullSpace.ProjSublattices L n k ∧
      ∀ i < k, ∀ e : FullSpace.Edge L k (i + 1), e.IsPositivelyOriented →
        FullSpace.ProjPreservesSets L n k i e
end YangMills.Construction.Tower
end
