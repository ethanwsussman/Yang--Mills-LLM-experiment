import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Dirichlet.HolderProduct
variable {d : ℕ} {S ξ : ℝ}
def productConstant (α s : ℝ) (ζ : LatticeSite d S ξ → ℝ) (D₀ D₁ : ℝ) : ℝ :=
  (scaledHolderSeminorm α s ζ + 2 * supNormAll ζ) * D₀ + supNormAll ζ * D₁
def HolderBoundOfProduct : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus S : ℝ), Parameters d L aMinus aPlus →
  ∀ (B : BlockSetting d L aMinus aPlus S) (α : ℝ), 0 ≤ α → α < 1 →
  ∀ y ∈ B.centres, ∀ (ζ D : LatticeSite d S B.ξ → ℝ) (D₀ D₁ : ℝ),
    (∀ x : LatticeSite d S B.ξ, B.centreSpacing y ≤ supNorm ((x : PeriodicTorus d S) - y) → ζ x = 0) →
    (∀ x : LatticeSite d S B.ξ, supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * B.centreSpacing y → |D x| ≤ D₀) →
    (∀ x x' : LatticeSite d S B.ξ, supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * B.centreSpacing y →
      supNorm ((x' : PeriodicTorus d S) - y) ≤ 2 * B.centreSpacing y →
      |D x - D x'| ≤ D₁ * (siteLOneDist x x' / B.centreSpacing y) ^ α) →
    (∀ x x' : LatticeSite d S B.ξ, x ≠ x' →
      |(ζ * D) x - (ζ * D) x'| ≤
        productConstant α (B.centreSpacing y) ζ D₀ D₁ * (siteLOneDist x x' / B.centreSpacing y) ^ α) ∧
    holderSeminorm α (ζ * D) ≤ B.centreSpacing y ^ (-α) * productConstant α (B.centreSpacing y) ζ D₀ D₁
end YangMills.Construction.Dirichlet.HolderProduct
