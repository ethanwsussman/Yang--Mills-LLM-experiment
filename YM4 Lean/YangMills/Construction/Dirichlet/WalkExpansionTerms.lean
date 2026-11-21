import YangMills.Construction.Dirichlet.CubePartitionOfUnity
import YangMills.Construction.Dirichlet.GreenBoundsOnRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
namespace WalkExpansion
def remainderConstC (d L : ℕ) (aMinus aPlus : ℝ) : ℝ :=
  remainderConst d L aPlus (PartitionOfUnity.partitionConst d)
    (RegionBounds.decayConstant d L aMinus aPlus)
def crossConstC (d L : ℕ) (aMinus aPlus : ℝ) : ℝ :=
  crossConst d L aPlus (PartitionOfUnity.partitionConst d)
    (RegionBounds.decayConstant d L aMinus aPlus)
def walkConstC (d L : ℕ) (aMinus aPlus : ℝ) : ℝ :=
  walkConst d L aMinus aPlus (PartitionOfUnity.partitionConst d)
    (RegionBounds.decayConstant d L aMinus aPlus)
def blockThreshold (d L : ℕ) (aMinus aPlus : ℝ) : ℝ :=
  blockLowerBound d L aMinus aPlus (PartitionOfUnity.partitionConst d)
    (RegionBounds.decayConstant d L aMinus aPlus)
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
def IsAboveThresholds : Prop :=
  blockThreshold d L aMinus aPlus ≤ (𝒮.M : ℝ) ∧
    gapLowerBound d L aMinus aPlus ≤ (𝒮.R₁ : ℝ) * (𝒮.M : ℝ)
def fieldMaxAbs {ξ : ℝ} (F : BondField d S ξ) (x : LatticeSite d S ξ) : ℝ := ⨆ μ, |F μ x|
structure IsGreenTestData (y y' : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ)
    (F : BondField d S 𝒮.ξ) (ζ : LatticeSite d S 𝒮.ξ → ℝ) : Prop where
  left_mem : y ∈ 𝒮.centres
  right_mem : y' ∈ 𝒮.centres
  fn_vanishesOff : VanishesOff (𝒮.cell y') f
  field_supportedNear : 𝒮.IsFieldSupportedNear y' F
  cutoff_eq_zero : ∀ x : LatticeSite d S 𝒮.ξ,
    𝒮.centreSpacing y ≤ supNorm ((x : PeriodicTorus d S) - y) → ζ x = 0
def divSource (F : BondField d S 𝒮.ξ) : LatticeSite d S 𝒮.ξ → ℝ :=
  restrictTo (𝒮.Ω 0) (latticeDiv F)
def holderWeight (α : ℝ) (y : PeriodicTorus d S) (ζ : LatticeSite d S 𝒮.ξ → ℝ) : ℝ :=
  𝒮.centreSpacing y ^ (1 - α) * (scaledHolderSeminorm α (𝒮.centreSpacing y) ζ + supNormAll ζ)
def cutoffGrad (ζ g : LatticeSite d S 𝒮.ξ → ℝ) : BondField d S 𝒮.ξ :=
  fun μ => pointwiseMul ζ (grad g μ)
def walkSum (m : ℕ) (v : List (CentredCube d S) → ℝ) : ℝ :=
  ∑ᶠ ω ∈ {ω : List (CentredCube d S) | 𝒮.IsCubeWalk ω ∧ BlockSetting.walkSteps ω = m}, v ω
def walkPower (m : ℕ) : ℝ := (walkConstC d L aMinus aPlus / (𝒮.M : ℝ)) ^ m
def remainderChain (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ)) (ω : List (CentredCube d S)) :
    (LatticeSite d S 𝒮.ξ → ℝ) → LatticeSite d S 𝒮.ξ → ℝ :=
  ω.foldr (fun Q T => 𝒮.cubeRemainder E Q ∘ T) id
end WalkExpansion
end YangMills.Construction.Dirichlet
