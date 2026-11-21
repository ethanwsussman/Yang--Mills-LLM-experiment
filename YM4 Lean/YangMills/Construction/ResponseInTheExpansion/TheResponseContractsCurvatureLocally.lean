import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames WeightedResponses RenormalizationStepParameters StepSettings StepCosts
  TorusFields TorusLumps
namespace ResponseInTheExpansion
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def ResponseLocalCurvatureContractionAt : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ ρ : ℕ, 16 ≤ ρ → 2 * ρ + 2 < n →
    ∀ (Y : TorusSite n) (A : TorusBond n → ℝ) (s sA : ℝ),
    (∀ p ∈ plaquettesIn ((Finset.univ : Finset (TorusSite n)).filter fun z => supDist z Y ≤ ρ), |curl A p| ≤ s) →
    (∀ b, |A b| ≤ sA) →
    ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * (Tb.stepParameters y).side))),
      (∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, supDist (parentBlock (Tb.stepParameters y).side z) Y ≤ 1) →
      |curl (responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u A) p| ≤
        s / 8 + C * Real.exp (-(c * (ρ : ℝ))) * sA
def responseLocalCurvatureContractionStatement : Prop :=
  HoldsOnParameterFamilies ResponseLocalCurvatureContractionAt
end ResponseInTheExpansion
end YangMills.Construction
end
