import YangMills.Construction.Dirichlet.WalkExpansionTerms
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.RemainderNeumann
variable {d L : ℕ} {S aLo aHi : ℝ}
structure Conclusions (𝒮 : BlockSetting d L aLo aHi S)
    (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ)) : Prop where
  resolvent_exists : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    ∃! u : LatticeSite d S 𝒮.ξ → ℝ,
      VanishesOff (𝒮.Ω 0) u ∧ u - 𝒮.totalRemainder E u = f
  fullGreen_eq_approxGreen : ∀ f u : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    VanishesOff (𝒮.Ω 0) u → u - 𝒮.totalRemainder E u = f →
      𝒮.fullGreen f = 𝒮.approxGreen E u
  hasSum_neumann : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    ∀ x, HasSum (fun n : ℕ => 𝒮.approxGreen E ((𝒮.totalRemainder E)^[n] f) x) (𝒮.fullGreen f x)
def Claim : Prop :=
  ∀ (d L : ℕ) (aLo aHi : ℝ), Parameters d L aLo aHi →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aLo aHi S), WalkExpansion.IsAboveThresholds 𝒮 →
    ∀ E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ), 𝒮.IsRuleFamily E → Conclusions 𝒮 E
end YangMills.Construction.Dirichlet.RemainderNeumann
