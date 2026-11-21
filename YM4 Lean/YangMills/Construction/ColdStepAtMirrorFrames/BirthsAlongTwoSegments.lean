import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def gibbsMean {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (A H : Ω → ℝ) : ℝ :=
  (∫ ω, H ω * Real.exp (- A ω) ∂μ) / ∫ ω, Real.exp (- A ω) ∂μ
def LogPartitionTwoSegmentsLocalDecomposition : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (P : Type) [Fintype P]
    (ψ q G : P → Ω → ℝ) (M : ℝ), μ ≠ 0 → (∀ Y, Measurable (ψ Y)) → (∀ Y, Measurable (q Y)) →
    (∀ Y, Measurable (G Y)) → (∀ Y ω, |ψ Y ω| ≤ M) → (∀ Y ω, |q Y ω| ≤ M) → (∀ Y ω, |G Y ω| ≤ M) →
    Real.log (∫ ω, Real.exp (-(∑ Y, ψ Y ω - ∑ Y, G Y ω)) ∂μ) -
        Real.log (∫ ω, Real.exp (-(∑ Y, q Y ω)) ∂μ) =
      ∑ Y, ((- ∫ τ in (0 : ℝ)..1, gibbsMean μ
          (fun ω => τ * ∑ Z, ψ Z ω + (1 - τ) * ∑ Z, q Z ω) (fun ω => ψ Y ω - q Y ω)) +
        ∫ ν in (0 : ℝ)..1, gibbsMean μ (fun ω => ∑ Z, ψ Z ω - ν * ∑ Z, G Z ω) (G Y))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
