import YangMills.Construction.Dirichlet.WalkExpansionTerms
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.RemainderNorm
variable {d L : ℕ} {S aLo aHi : ℝ}
structure Conclusions (𝒮 : BlockSetting d L aLo aHi S)
    (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ)) : Prop where
  vanishesOff : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    VanishesOff (𝒮.Ω 0) (𝒮.totalRemainder E f)
  supNorm_le : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    supNormAll (𝒮.totalRemainder E f) ≤
      WalkExpansion.walkConstC d L aLo aHi * (𝒮.M : ℝ)⁻¹ * supNormAll f
  map_add : ∀ f u : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    VanishesOff (𝒮.Ω 0) u → 𝒮.totalRemainder E (f + u) = 𝒮.totalRemainder E f + 𝒮.totalRemainder E u
  map_smul : ∀ (r : ℝ) (f : LatticeSite d S 𝒮.ξ → ℝ), VanishesOff (𝒮.Ω 0) f →
    𝒮.totalRemainder E (r • f) = r • 𝒮.totalRemainder E f
def Claim : Prop :=
  ∀ (d L : ℕ) (aLo aHi : ℝ), Parameters d L aLo aHi →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aLo aHi S), WalkExpansion.IsAboveThresholds 𝒮 →
    ∀ E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ), 𝒮.IsRuleFamily E → Conclusions 𝒮 E
end YangMills.Construction.Dirichlet.RemainderNorm
