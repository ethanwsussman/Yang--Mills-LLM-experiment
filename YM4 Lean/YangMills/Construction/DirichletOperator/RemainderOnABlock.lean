import YangMills.Construction.Dirichlet.WalkExpansionTerms
import YangMills.Construction.Dirichlet.WeightedDistance
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.LocalRemainderBound
def Claim : Prop :=
  ∀ (d L : ℕ) (aLo aHi : ℝ), Parameters d L aLo aHi →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aLo aHi S), WalkExpansion.IsAboveThresholds 𝒮 →
    ∀ E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ), 𝒮.IsRuleFamily E →
    ∀ Q ∈ 𝒮.coverCubes, ∀ y ∈ 𝒮.centres, ∀ y' ∈ 𝒮.centres,
    ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.cell y') f →
      (∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y →
        |𝒮.cubeRemainder E Q f x| ≤
          WalkExpansion.remainderConstC d L aLo aHi * (𝒮.M : ℝ)⁻¹ *
            WeightedDistance.expDecay 𝒮 (expDecayRate d L aLo aHi / 2) y y' * supNormAll f) ∧
      (y' ∉ 𝒮.centresNearBump Q → 𝒮.cubeRemainder E Q f = 0) ∧
      (y ∉ 𝒮.centresNearBump Q → ∀ x : LatticeSite d S 𝒮.ξ,
        (x : PeriodicTorus d S) ∈ 𝒮.cell y → 𝒮.cubeRemainder E Q f x = 0)
end YangMills.Construction.Dirichlet.LocalRemainderBound
