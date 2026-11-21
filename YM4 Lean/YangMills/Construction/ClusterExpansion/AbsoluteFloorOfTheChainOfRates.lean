import YangMills.Construction.ClusterExpansion.TheChainOfRates
import YangMills.Construction.Parameters.ConstructionParameters
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ParameterChoice YangMills.Construction.ClusterExpansion.TwoLevelStep YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.RateChain
noncomputable section
namespace YangMills.Construction.PeriodicLattice.UniformRateChainThreshold
structure RateChainFloors (βs δw : ℝ) (L : ℕ) : Prop where
  growthBound : 2 * 338 * 169 * hullGrowthConstant * (1 + 4 * βs) / (1 - 2 * δw) ≤ (L : ℝ) - 1
  sizeBound : 4 + 32 * (1 + 4 * βs) / (1 - 2 * δw) ≤ (L : ℝ)
  coarseningBound : 1 + 2 * hullGrowthConstant * (1 + 4 * βs) ≤ (L : ℝ)
  chainBound : blockingFactorThreshold δw ≤ (L : ℝ)
def IsUniformThreshold (t : ℝ) : Prop :=
  ∀ (βs rStar : ℝ) (L : ℕ), 0 < βs → βs ≤ 1 / 4 → 0 < rStar → t ≤ (L : ℝ) →
    RateChainFloors βs (windowWidth rStar L) L
end YangMills.Construction.PeriodicLattice.UniformRateChainThreshold
end
