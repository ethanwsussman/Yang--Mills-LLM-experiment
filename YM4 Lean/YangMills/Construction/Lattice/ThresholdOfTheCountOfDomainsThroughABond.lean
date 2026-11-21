import YangMills.Construction.Lattice.CountOfTheDomainsThroughABond
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
structure IsDomainCountThreshold (κ : ℝ) : Prop where
  countingRate_lt : PolymerActivities.DomainCounting.countingRate < κ
  bound : ∀ κ' : ℝ, κ ≤ κ' → ∀ (S : LevelUnitPartition) (b : S.Bond) (𝒟),
    S.IsDomainFamily 𝒟 → S.DomainCountBoundAt κ κ' 𝒟 b
  bound_of_fraction : ∀ δ ϰ : ℝ, δ < 1 / 2 → κ / (1 - 2 * δ) ≤ ϰ →
    ∀ (S : LevelUnitPartition) (b : S.Bond) (𝒟),
      S.IsDomainFamily 𝒟 → S.DomainCountBoundAt κ ((1 - 2 * δ) * ϰ) 𝒟 b
end YangMills.Construction.PeriodicLattice
end
