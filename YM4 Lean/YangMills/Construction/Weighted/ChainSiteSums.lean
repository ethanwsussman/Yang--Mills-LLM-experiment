import YangMills.Construction.Weighted.GreenSquareConstants
import YangMills.Construction.Weighted.SeparatedRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
def TorusData.scaleRatioRate (D : TorusData) : ℝ :=
  Real.log (D.L : ℝ) / ((D.gapNumber : ℝ) * (D.blockNumber : ℝ))
def ChainSiteSumBounds : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D),
    AntitoneOn (latticeSumConst 4 D.L) (Ioi 0) ∧
    AntitoneOn (latticeSumRadius 4 D.L) (Ioi 0) ∧
    (∀ n n' : ℕ, ∀ x ∈ B.layer n, ∀ x' ∈ B.layer n',
      (D.gapNumber : ℝ) * (D.blockNumber : ℝ) * max (|(n : ℝ) - (n' : ℝ)| - 1) 0 ≤
        B.weightedDistance x x') ∧
    (∀ s : ℝ, ∀ y ∈ B.allSites, ∀ y' ∈ B.allSites,
      (B.siteScale y / B.siteScale y') ^ s ≤
        (D.L : ℝ) ^ |s| * Real.exp (|s| * D.scaleRatioRate * B.weightedDistance y y')) ∧
    (∀ κ : ℝ, 0 < κ → latticeSumRadius 4 D.L κ ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ) →
      (∀ y : ↥B.allSites,
        ∑ᶠ y' : ↥B.allSites, Real.exp (-κ * B.weightedDistance y y') ≤
          latticeSumConst 4 D.L κ) ∧
      (∀ y y' : ↥B.allSites,
        ∑ᶠ y'' : ↥B.allSites,
            Real.exp (-(2 * κ) * B.weightedDistance y y'') *
              Real.exp (-(2 * κ) * B.weightedDistance y'' y') ≤
          latticeSumConst 4 D.L κ * Real.exp (-κ * B.weightedDistance y y')))
end YangMills.Construction.Weighted
