import YangMills.Construction.Dirichlet.WalkExpansionTerms
import YangMills.Construction.Dirichlet.WeightedDistance
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.ThresholdConsequences
variable {d L : ℕ} {S aLo aHi : ℝ}
structure Conclusions (𝒮 : BlockSetting d L aLo aHi S) : Prop where
  blockSize_floor : 3 * L * (L + 12) ≤ 𝒮.M
  gap_floor : L * (L + 9) ≤ 𝒮.R₁ * 𝒮.M
  floors : BlockGapFloors d L aLo aHi (𝒮.M : ℝ) (𝒮.R₁ : ℝ)
  sumRate_floor : WeightedDistance.RateAboveFloor 𝒮 (sumRate d L aLo aHi)
  partitionConst_nonneg : 0 ≤ PartitionOfUnity.partitionConst d
  one_le_sumBound : 1 ≤ sumBound d L aLo aHi
  remainderConst_nonneg : 0 ≤ WalkExpansion.remainderConstC d L aLo aHi
  crossConst_nonneg : 0 ≤ WalkExpansion.crossConstC d L aLo aHi
  walkConst_pos : 0 < WalkExpansion.walkConstC d L aLo aHi
  remainderConst_le_walkConst :
    WalkExpansion.remainderConstC d L aLo aHi ≤ WalkExpansion.walkConstC d L aLo aHi
  crossConst_le_walkConst :
    WalkExpansion.crossConstC d L aLo aHi ≤ WalkExpansion.walkConstC d L aLo aHi
  two_mul_walkConst_le : 2 * WalkExpansion.walkConstC d L aLo aHi ≤ (𝒮.M : ℝ)
def Claim : Prop :=
  ∀ (d L : ℕ) (aLo aHi : ℝ), Parameters d L aLo aHi →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aLo aHi S), WalkExpansion.IsAboveThresholds 𝒮 → Conclusions 𝒮
end YangMills.Construction.Dirichlet.ThresholdConsequences
