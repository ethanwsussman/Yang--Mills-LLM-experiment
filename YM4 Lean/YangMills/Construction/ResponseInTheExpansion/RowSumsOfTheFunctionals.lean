import YangMills.Construction.ResponseInTheExpansion.LocalChainAboveALevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
namespace ResponseInTheExpansion
open TorusLumps TorusFields RenormalizationStepParameters StepSettings WeightedResponses
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def transportedCurlFunctionalBoundsAt : Prop :=
  (∀ (k d n : ℕ) [NeZero n], Tb.n₀ ≤ n →
    ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side d n))),
    (∀ (B : TorusBond n → ℝ) (s : ℝ),
      (∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |WeightedResponses.curl B p'| ≤ s) →
      |∑ c, adjointTransport Tb.coupling Tb.ρA (Tb.stepParameters y).side k d n (curlFunctional p) c * B c| ≤
        (1 / 2 : ℝ) ^ d * s) ∧
    ∑ b, |adjointTransport Tb.coupling Tb.ρA (Tb.stepParameters y).side k d n (curlFunctional p) b| ≤
      4 * (1 / 2 : ℝ) ^ d) ∧
  ∃ c x₀ : ℝ, 0 < c ∧ ∀ (x r : ℝ) (k d n : ℕ) [NeZero n], x₀ ≤ x → 0 ≤ r → Tb.n₀ ≤ n → d < chainDepth x →
    ∀ (o : TorusSite (fineSide (Tb.stepParameters y).side (d + 1) n)),
    ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side (d + 1) n))),
      p.1 ∈ supBall o (19 * r) →
      ∑ b ∈ (Finset.univ : Finset (TorusBond (n * (Tb.stepParameters y).side))).filter
          (fun b => parentBlock (Tb.stepParameters y).side b.1 ∉ supBall
            (siteAbove (Tb.stepParameters y).side (d + 1) n o)
            (ballRadius (Tb.stepParameters y).side r (logCubeScale x) (d + 1) - 3 * logCubeScale x)),
        |adjointTransport Tb.coupling Tb.ρA (Tb.stepParameters y).side k d (n * (Tb.stepParameters y).side)
          (curlFunctional p) b| ≤ Real.exp (-(c * logCubeScale x))
def transportedCurlFunctionalBoundsStatement : Prop := HoldsOnParameterFamilies transportedCurlFunctionalBoundsAt
end ResponseInTheExpansion
end YangMills.Construction
end
