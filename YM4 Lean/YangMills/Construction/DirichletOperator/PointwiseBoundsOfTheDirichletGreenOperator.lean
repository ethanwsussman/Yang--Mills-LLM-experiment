import YangMills.Construction.Dirichlet.WalkExpansionTerms
import YangMills.Construction.Dirichlet.WeightedDistance
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.GreenPointwise
variable {d L : ℕ} {S aLo aHi : ℝ}
structure Conclusions (𝒮 : BlockSetting d L aLo aHi S) (B : ℝ) (Bα : ℝ → ℝ) : Prop where
  at_sites : ∀ (y y' : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ)
    (F : BondField d S 𝒮.ξ) (η : LatticeSite d S 𝒮.ξ → ℝ),
    WalkExpansion.IsGreenTestData 𝒮 y y' f F η →
    ∀ x : LatticeSite d S 𝒮.ξ,
      supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y →
      |𝒮.fullGreen f x| ≤ B * 𝒮.centreSpacing y ^ 2 *
          WeightedDistance.expDecay 𝒮 (expDecayRate d L aLo aHi / 2) y y' * supNormAll f ∧
      WalkExpansion.fieldMaxAbs (grad (𝒮.fullGreen f)) x ≤ B * 𝒮.centreSpacing y *
          WeightedDistance.expDecay 𝒮 (expDecayRate d L aLo aHi / 2) y y' * supNormAll f ∧
      |𝒮.fullGreen (WalkExpansion.divSource 𝒮 F) x| ≤ B * 𝒮.centreSpacing y *
          WeightedDistance.expDecay 𝒮 (expDecayRate d L aLo aHi / 2) y y' * fieldSupNorm F
  laplacian : ∀ (y y' : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ)
    (F : BondField d S 𝒮.ξ) (η : LatticeSite d S 𝒮.ξ → ℝ),
    WalkExpansion.IsGreenTestData 𝒮 y y' f F η →
    ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y →
      |latticeLaplacian (𝒮.fullGreen f) x| ≤ B *
        WeightedDistance.expDecay 𝒮 (expDecayRate d L aLo aHi / 2) y y' * supNormAll f
  holder : ∀ (y y' : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ)
    (F : BondField d S 𝒮.ξ) (η : LatticeSite d S 𝒮.ξ → ℝ),
    WalkExpansion.IsGreenTestData 𝒮 y y' f F η →
    ∀ α : ℝ, 0 < α → α < 1 →
      fieldHolderSeminorm α (WalkExpansion.cutoffGrad 𝒮 η (𝒮.fullGreen f)) ≤
          Bα α * WalkExpansion.holderWeight 𝒮 α y η *
          WeightedDistance.expDecay 𝒮 (expDecayRate d L aLo aHi / 2) y y' * supNormAll f ∧
      holderSeminorm α (pointwiseMul η (𝒮.fullGreen (WalkExpansion.divSource 𝒮 F))) ≤
        Bα α * WalkExpansion.holderWeight 𝒮 α y η *
          WeightedDistance.expDecay 𝒮 (expDecayRate d L aLo aHi / 2) y y' * fieldSupNorm F
def Claim : Prop :=
  ∀ (d L : ℕ) (aLo aHi : ℝ), Parameters d L aLo aHi →
    ∀ (B : ℝ) (Bα : ℝ → ℝ),
      1 + (1 + aHi) * RegionBounds.decayConstant d L aLo aHi ≤ B →
      (∀ α : ℝ, 0 < α → α < 1 →
        2 * RegionBounds.decayConstant d L aLo aHi +
          RegionBounds.holderDecayConstant d L aLo aHi α ≤ Bα α) →
      ∀ (S : ℝ) (𝒮 : BlockSetting d L aLo aHi S), WalkExpansion.IsAboveThresholds 𝒮 →
        Conclusions 𝒮 B Bα
end YangMills.Construction.Dirichlet.GreenPointwise
