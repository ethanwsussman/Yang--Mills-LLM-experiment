import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import YangMills.Construction.WeightedGreen.IntegerExpSums
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.WeightedDistance
variable {d L : ℕ} {S aLow aHigh : ℝ} (𝒮 : BlockSetting d L aLow aHigh S)
def RateAboveFloor (κ : ℝ) : Prop :=
  1 / 4 * κ * (𝒮.R₁ : ℝ) * (𝒮.M : ℝ) ≥
    2 * (d : ℝ) * Real.log (intExpSum (1 / 2 * κ)) + 1 / 4 * κ * (d : ℝ) * ((L : ℝ) + 3) +
      Real.log 2 + 1
def expDecay (κ : ℝ) (y y' : PeriodicTorus d S) : ℝ := Real.exp (-κ * 𝒮.blockDist y y')
def pathProduct (κ : ℝ) {N : ℕ} (y : Fin (N + 1) → PeriodicTorus d S) : ℝ :=
  ∏ i : Fin N, expDecay 𝒮 κ (y i.castSucc) (y i.succ)
end YangMills.Construction.Dirichlet.WeightedDistance
