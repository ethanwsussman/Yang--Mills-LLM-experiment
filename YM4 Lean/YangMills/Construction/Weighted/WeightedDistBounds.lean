import YangMills.Construction.Weighted.BareLatticeBonds
import YangMills.Construction.Weighted.GivenChain
import YangMills.Construction.Weighted.LengthDensity
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def LipschitzBoundedByWeightedDist : Prop :=
  ∀ f : D.Space → ℝ, LipschitzL1 f →
    (∀ (Γ : List LiftedSegment) (x x' : D.Space), IsTreeGraph D.side Γ →
      x ∈ segmentsSupport D.side Γ → x' ∈ segmentsSupport D.side Γ →
        ENNReal.ofReal |f x - f x'| ≤
          setLIntegralL1 (segmentsSupport D.side Γ) (localLip f)) ∧
    ∀ τ : ℝ, 0 ≤ τ →
      (∀ x, localLip f x ≤ ENNReal.ofReal (τ * B.weightDensity x)) →
        ∀ x x' : D.Space, |f x - f x'| ≤ τ * B.weightedDistance x x'
def WeightDensityLowerBound : Prop :=
  ∀ (n : ℕ) (x : D.Space), x ∉ B.stage (n + 1) → (D.scale n)⁻¹ ≤ B.weightDensity x
def WeightedDistLowerBoundFromSet : Prop :=
  ∀ (A : Set D.Space) (ρ : ℝ) (n : ℕ), IsClosed A → A.Nonempty → 0 < ρ →
    (∀ x : D.Space, setSupDist {x} A ≤ ENNReal.ofReal ρ → x ∉ B.stage (n + 1)) →
      ∀ x ∈ A, ∀ x' : D.Space, ENNReal.ofReal ρ ≤ setSupDist {x'} A →
        ρ / D.scale n ≤ B.weightedDistance x x'
def BlocksAndBondsShort : Prop :=
  (∀ y ∈ B.allSites, ∀ x ∈ B.block y, B.weightedDistance (x : D.Space) y ≤ 1 / 2 * 4) ∧
  ∀ x x' : D.BareSite, x ∈ D.bareSites (B.stage 0) → x' ∈ D.bareSites (B.stage 0) →
    TorusData.Adjacent x x' →
      |(B.bareLevel x : ℤ) - (B.bareLevel x' : ℤ)| ≤ 1 ∧
      B.weightedDistance (x : D.Space) (x' : D.Space) ≤
        1 / 2 * D.scale 0 * ((B.bareScale x)⁻¹ + (B.bareScale x')⁻¹) ∧
      1 / 2 * D.scale 0 * ((B.bareScale x)⁻¹ + (B.bareScale x')⁻¹) ≤
        min 1 ((D.L : ℝ) * D.scale 0 * (B.bareScale x)⁻¹)
def WeightedDistGeL1 : Prop :=
  ∀ x x' : D.Space, (D.scale D.top)⁻¹ * torusL1Norm (x - x') ≤ B.weightedDistance x x'
end SeparatedChain
def WeightedDistBounds : Prop :=
  ∀ G : GivenChain,
    G.chain.LipschitzBoundedByWeightedDist ∧
    G.chain.WeightDensityLowerBound ∧
    G.chain.WeightedDistLowerBoundFromSet ∧
    G.chain.BlocksAndBondsShort ∧
    G.chain.WeightedDistGeL1
end YangMills.Construction.Weighted
end
