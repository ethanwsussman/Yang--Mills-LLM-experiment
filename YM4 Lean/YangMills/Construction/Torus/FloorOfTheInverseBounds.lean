import YangMills.Construction.SeparatedSequences.InverseGreenConstants
import YangMills.Construction.Torus.GreenOperatorBoundsOnTheTori
import YangMills.Construction.Torus.PropertiesOfTheWeightedDistanceAndCells
import Mathlib
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace InverseBounds
open SeparatedSequences GreenBounds
def decayRateOfInverse (L : ℕ) : ℝ :=
  inverseDecayRate 4 L (chosen L).rate (chosen L).bound
def productThreshold (L : ℕ) : ℝ :=
  gapBlockThreshold 4 L (chosen L).rate (chosen L).bound (chosen L).gapLower
def RateThresholdOrdered (L : ℕ) : Prop :=
  0 < decayRateOfInverse L ∧ decayRateOfInverse L ≤ (chosen L).rate / 4 ∧
    (chosen L).gapLower ≤ productThreshold L
def ExpSumsBounded (W : GaugeSetting) : Prop :=
  ∀ α : ℝ, 1 / 2 * decayRateOfInverse W.data.L ≤ α →
    ∀ y ∈ W.chain.shellSitesUnion,
      ∑ᶠ y' : ↥W.chain.shellSitesUnion, Real.exp (-α * W.chain.scaledDist y y') ≤
          expSumConstant 4 W.data.L α ∧
      ∑ᶠ c' : W.CoarseBond, Real.exp (-α * GaugeSetting.siteCoarseDist y c') ≤
          2 * 4 * expSumConstant 4 W.data.L α
def PowerDistanceTrade (W : GaugeSetting) : Prop :=
  ∀ n n' : ℕ, n ≤ W.data.lastLevel → n' ≤ W.data.lastLevel →
    ∀ y ∈ W.chain.augmentedShell n, ∀ y' ∈ W.chain.augmentedShell n',
      ∀ s ε : ℝ, |s| ≤ 4 → 1 / 2 * decayRateOfInverse W.data.L ≤ ε →
        (W.data.L : ℝ) ^ (s * ((n' : ℝ) - (n : ℝ))) *
            Real.exp (-ε * W.chain.scaledDist y y') ≤
          (W.data.L : ℝ) ^ |s|
end InverseBounds
def InverseBoundsStatement : Prop :=
  (∀ L : ℕ, Blocking.DimFourOddBlockingFactorGeThirteen 4 L →
    InverseBounds.RateThresholdOrdered L) ∧
  ∀ W : GaugeSetting, W.data.L ≤ W.data.blockCount →
    InverseBounds.productThreshold W.data.L ≤
        (W.data.gapCount : ℝ) * (W.data.blockCount : ℝ) →
      InverseBounds.ExpSumsBounded W ∧ InverseBounds.PowerDistanceTrade W
end YangMills.Construction.GeneralTorus
end
