import YangMills.Construction.Dirichlet.WalkExpansionTerms
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.CubeParametrix
def Claim : Prop :=
  ∀ (d L : ℕ) (aLo aHi : ℝ), Parameters d L aLo aHi →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aLo aHi S), WalkExpansion.IsAboveThresholds 𝒮 →
    ∀ E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ), 𝒮.IsRuleFamily E →
    ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
      𝒮.fullOperator (𝒮.approxGreen E f) = f - 𝒮.totalRemainder E f
end YangMills.Construction.Dirichlet.CubeParametrix
