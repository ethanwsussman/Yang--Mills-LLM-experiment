import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import YangMills.Construction.WeightedGreen.DecayRateDefs
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.RegionEnergy
variable {d L : ℕ} {S aLow aHigh : ℝ}
def bondsTouching {ξ : ℝ} (W : Set (PeriodicTorus d S)) : Set (LatticeBond d S ξ) :=
  {b | (b.source : PeriodicTorus d S) ∈ W ∨ (b.target : PeriodicTorus d S) ∈ W}
open Classical in
def endpointValue {ξ : ℝ} (W : Set (PeriodicTorus d S)) (φ : LatticeSite d S ξ → ℝ)
    (b : LatticeBond d S ξ) : ℝ :=
  if (b.source : PeriodicTorus d S) ∈ W then φ b.source else φ b.target
def expWeightedFieldNorm {ξ : ℝ} (W : Set (PeriodicTorus d S)) (θ : ℝ)
    (φ : LatticeSite d S ξ → ℝ) (F : BondField d S ξ) : ℝ :=
  √(ξ ^ d * ∑ᶠ b ∈ bondsTouching (ξ := ξ) W,
    Real.exp (2 * θ * endpointValue W φ b) * |F b.dir b.source| ^ 2)
variable (𝒮 : BlockSetting d L aLow aHigh S)
def sqrtWeighted (g : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  fun x => 𝒮.localWeight x ^ (1 / 2 : ℝ) * g x
structure IsAdmissibleField (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S 𝒮.ξ))
    (F : BondField d S 𝒮.ξ) : Prop where
  boundary_vanish : ∀ b : LatticeBond d S 𝒮.ξ, IsBoundaryBond W b → b ∉ E → F b.dir b.source = 0
  far_vanish : ∀ b : LatticeBond d S 𝒮.ξ, b ∉ bondsTouching (ξ := 𝒮.ξ) W → F b.dir b.source = 0
end YangMills.Construction.Dirichlet.RegionEnergy
