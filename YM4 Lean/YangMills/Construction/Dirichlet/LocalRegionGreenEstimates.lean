import YangMills.Construction.Dirichlet.RegionEnergyEstimate
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
open YangMills.Construction.Dirichlet.RegionEnergy
noncomputable section
namespace YangMills.Construction.Dirichlet.LocalRegion
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
def outerBox (W : Set (PeriodicTorus d S)) (y : PeriodicTorus d S) : Set (PeriodicTorus d S) :=
  {x | x ∈ W ∧ supNorm (x - y) ≤ ((L : ℝ) + 8) * 𝒮.centreSpacing y}
def fieldSupNormOn (X : Set (PeriodicTorus d S)) (F : BondField d S 𝒮.ξ) : ℝ :=
  sSup {r | ∃ b ∈ bondsTouching (ξ := 𝒮.ξ) X, r = |F b.dir b.source|}
def localScale (W : Set (PeriodicTorus d S)) (y : PeriodicTorus d S) (u f : LatticeSite d S 𝒮.ξ → ℝ)
    (F : BondField d S 𝒮.ξ) : ℝ :=
  𝒮.centreSpacing y ^ (-(d : ℝ) / 2) * siteNormOn (outerBox 𝒮 W y) u +
    𝒮.centreSpacing y ^ 2 * supNormOn (𝒮.collar y) f +
    𝒮.centreSpacing y * fieldSupNormOn 𝒮 (𝒮.collar y) F
def IsCloseTo (y : PeriodicTorus d S) (x : LatticeSite d S 𝒮.ξ) : Prop :=
  supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y
def holderFactor (α : ℝ) (y : PeriodicTorus d S) (x x' : LatticeSite d S 𝒮.ξ) : ℝ :=
  (siteLOneDist x x' / 𝒮.centreSpacing y) ^ α
end YangMills.Construction.Dirichlet.LocalRegion
