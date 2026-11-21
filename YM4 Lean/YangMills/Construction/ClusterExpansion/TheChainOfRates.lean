import YangMills.Construction.ClusterExpansion.AnchoredPairsOfExemptFamilies
import YangMills.Construction.ClusterExpansion.HullLengthOfTheDomainOfAConfigurationOfAHistoryWithAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ClusterExpansion.TwoLevelStep
namespace PeriodicLattice.RateChain
def activityDecayRate (δ κ : ℝ) : ℝ := (1 - 2 * δ) * κ - 1
def RateChainInequality (δ : ℝ) (L : ℕ) (cP κ : ℝ) : Prop :=
  hullLengthConfigurationConstant / ((L : ℝ) - 1) *
      (169 * κ + anchoredPairEntropyExponent hullOverlapBound + 13 + 16 * (cP + 4)) ≤
    (1 - 2 * δ) * κ - 1 - 2 * anchoredPairEntropyExponent hullOverlapBound
def blockingFactorThreshold (δ : ℝ) : ℝ :=
  1 + 2 * 169 * hullLengthConfigurationConstant / (1 - 2 * δ)
end PeriodicLattice.RateChain
end YangMills.Construction
end
