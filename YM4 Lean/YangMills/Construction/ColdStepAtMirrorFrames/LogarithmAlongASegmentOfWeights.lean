import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
def LogPartitionInterpolation : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Ω → ℝ) (M : ℝ),
    μ ≠ 0 → Measurable A → Measurable B → (∀ ω, |A ω| ≤ M) → (∀ ω, |B ω| ≤ M) →
    Real.log (∫ ω, Real.exp (-(B ω)) ∂μ) - Real.log (∫ ω, Real.exp (-(A ω)) ∂μ) =
      - ∫ τ in (0 : ℝ)..1,
        (∫ ω, (B ω - A ω) * Real.exp (-(τ * B ω + (1 - τ) * A ω)) ∂μ) /
          ∫ ω, Real.exp (-(τ * B ω + (1 - τ) * A ω)) ∂μ
end YangMills.Construction.ColdStepAtMirrorFrames
end
