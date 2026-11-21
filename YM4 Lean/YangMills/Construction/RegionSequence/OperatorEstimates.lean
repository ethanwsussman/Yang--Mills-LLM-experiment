import YangMills.Construction.Dirichlet.GreenOperatorEstimates
import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import YangMills.Construction.Weighted.SeparatedSums
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet RegionSequence RegionSequence.NestedRegions
open DirichletGreen (fieldModulusAt)
namespace RegionSequence.OperatorEstimates
def kernelOf {ι : Type} (K : (ι → ℝ) → ι → ℝ) (x x' : ι) : ℝ :=
  K (indicator {x'} fun _ => 1) x
def avgGreenSq (𝒮 : NestedRegions) (ω : 𝒮.Coarse) : 𝒮.Coarse :=
  blockAvg (gaugeGreenOp (gaugeGreenOp (blockAvgAdj ω)))
def avgGreenSqInv (𝒮 : NestedRegions) (ω : 𝒮.Coarse) : 𝒮.Coarse :=
  inverseValue univ (avgGreenSq 𝒮) ω
def dirichletRate (L : ℕ) : ℝ :=
  (DirichletGreen.chosenConstants 4 L (1 - ((L : ℝ) ^ 2)⁻¹) 1).δ₀
structure Constants where
  δ : ℝ
  B : ℝ
  minBlock : ℝ
  minProduct : ℝ
instance : Inhabited Constants := ⟨⟨0, 0, 0, 0⟩⟩
structure DistanceAndSumBounds (𝒮 : NestedRegions) (M R₁ : ℕ) : Prop where
  dist_ge : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres,
    (R₁ : ℝ) * (M : ℝ) * max (|(𝒮.level y : ℝ) - (𝒮.level y' : ℝ)| - 1) 0 ≤
      𝒮.weightedDist y y'
  expSum_le : ∀ κ : ℝ, 0 < κ → Weighted.separatedSumRadius 4 𝒮.L κ ≤ (R₁ : ℝ) * (M : ℝ) →
    ∀ y : ↥𝒮.allCentres, ∑ᶠ y' : ↥𝒮.allCentres, Real.exp (-κ * 𝒮.weightedDist y y') ≤
      Weighted.separatedSumConst 4 𝒮.L κ
namespace Constants
variable (c : Constants) (𝒮 : NestedRegions)
def expFactor (y y' : 𝒮.Point) : ℝ := Real.exp (-c.δ * 𝒮.weightedDist y y')
structure KernelBounds : Prop where
  green_le : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, ∀ f ∈ 𝒮.siteFns, VanishesOff (𝒮.cellOf y') f →
    ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.cellOf y →
      |gaugeGreenOp f x| ≤ c.B * 𝒮.levelScale y ^ 2 * c.expFactor 𝒮 y y' * supNormAll f ∧
      fieldModulusAt (grad (gaugeGreenOp f)) x ≤
        c.B * 𝒮.levelScale y * c.expFactor 𝒮 y y' * supNormAll f
  greenDiv_le : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, ∀ F : BondField 4 𝒮.side 𝒮.ξ,
    (∀ ν, VanishesOff (𝒮.cellOf y') (F ν)) → ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.cellOf y →
      |gaugeGreenOp (projSites (latticeDiv F)) x| ≤
        c.B * 𝒮.levelScale y * c.expFactor 𝒮 y y' * fieldSupNorm F
  inverseKernel_le : ∀ y y' : ↥𝒮.allCentres, |kernelOf (avgGreenSqInv 𝒮) y y'| ≤
    c.B * (𝒮.levelScale y ^ 4)⁻¹ * c.expFactor 𝒮 y y'
  longKernel_le : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, ∀ b ∈ 𝒮.bonds, ∀ b' ∈ 𝒮.bonds,
    AnchoredIn (𝒮.cellOf y) b → AnchoredIn (𝒮.cellOf y') b' →
      |kernelOf longOp b b'| ≤
        c.B * (𝒮.ξ / 𝒮.levelScale y') ^ 4 * (𝒮.levelScale y ^ 2)⁻¹ * c.expFactor 𝒮 y y'
structure Valid (L : ℕ) : Prop where
  rate_pos : 0 < c.δ
  rate_le : c.δ ≤ 1 / 2 * dirichletRate L
  one_le_B : 1 ≤ c.B
  bounds : ∀ (𝒮 : NestedRegions) (M R₁ : ℕ), 𝒮.L = L → 𝒮.IsGapSeparated M R₁ → (𝒮.Ω 0).Nonempty →
    DistanceAndSumBounds 𝒮 M R₁ ∧
      (c.minBlock ≤ (M : ℝ) → c.minProduct ≤ (R₁ : ℝ) * (M : ℝ) → c.KernelBounds 𝒮)
end Constants
def chosenConstants (L : ℕ) : Constants := Classical.epsilon fun c : Constants => c.Valid L
end RegionSequence.OperatorEstimates
end YangMills.Construction
