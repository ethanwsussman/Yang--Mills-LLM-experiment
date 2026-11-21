import YangMills.Construction.Dirichlet.WalkExpansionTerms
import YangMills.Construction.Dirichlet.WeightedDistance
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
open YangMills.Construction.WeightedGreen YangMills.Construction.Dirichlet.WalkExpansion
noncomputable section
namespace YangMills.Construction.Dirichlet.FunctionWalkBounds
variable {d L : ℕ} {S aMinus aPlus : ℝ}
structure Bounds (𝒮 : BlockSetting d L aMinus aPlus S) (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ))
    (B : ℝ) (Bα : ℝ → ℝ) : Prop where
  pointwise : ∀ (m : ℕ) (y y' : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ)
    (F : BondField d S 𝒮.ξ) (ζ : LatticeSite d S 𝒮.ξ → ℝ), IsGreenTestData 𝒮 y y' f F ζ →
    ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y →
      walkSum 𝒮 m (fun ω => |𝒮.walkOperator E ω f x|) ≤
        walkPower 𝒮 m * B * 𝒮.centreSpacing y ^ 2 *
          WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 4) y y' * supNormAll f ∧
      walkSum 𝒮 m (fun ω => fieldMaxAbs (grad (𝒮.walkOperator E ω f)) x) ≤
        walkPower 𝒮 m * B * 𝒮.centreSpacing y *
          WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 4) y y' * supNormAll f ∧
      walkSum 𝒮 m (fun ω => |latticeLaplacian (𝒮.walkOperator E ω f) x|) ≤
        walkPower 𝒮 m * B *
          WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 4) y y' * supNormAll f
  holder : ∀ (m : ℕ) (y y' : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ)
    (F : BondField d S 𝒮.ξ) (ζ : LatticeSite d S 𝒮.ξ → ℝ), IsGreenTestData 𝒮 y y' f F ζ →
    ∀ α : ℝ, 0 < α → α < 1 →
      walkSum 𝒮 m (fun ω => fieldHolderSeminorm α (cutoffGrad 𝒮 ζ (𝒮.walkOperator E ω f))) ≤
        walkPower 𝒮 m * Bα α * holderWeight 𝒮 α y ζ *
          WeightedDistance.expDecay 𝒮 (expDecayRate d L aMinus aPlus / 4) y y' * supNormAll f
end YangMills.Construction.Dirichlet.FunctionWalkBounds
