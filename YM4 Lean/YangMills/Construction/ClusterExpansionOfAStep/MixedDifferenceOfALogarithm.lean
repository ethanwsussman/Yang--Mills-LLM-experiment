import YangMills.Construction.ColdStepAtMirrorFrames.BirthsAlongTwoSegments
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MixedDifferences
open YangMills.Construction.ColdStepAtMirrorFrames
def bilinearExponent {Ω : Type} (U A B C : Ω → ℝ) (v w : ℝ) (ω : Ω) : ℝ :=
  U ω + v * A ω + w * B ω + v * w * C ω
def LogIntegralMixedDifferenceBound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (U A B C : Ω → ℝ) (M ε : ℝ),
    μ ≠ 0 → Measurable U → Measurable A → Measurable B → Measurable C →
    (∀ ω, |U ω| ≤ M) → (∀ ω, |A ω| ≤ M) → (∀ ω, |B ω| ≤ M) → (∀ ω, |C ω| ≤ M) →
    (∀ v w : ℝ, 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
      |gibbsMean μ (bilinearExponent U A B C v w) (fun ω => (A ω + w * C ω) * (B ω + v * C ω)) -
          gibbsMean μ (bilinearExponent U A B C v w) (fun ω => A ω + w * C ω) *
            gibbsMean μ (bilinearExponent U A B C v w) (fun ω => B ω + v * C ω) -
          gibbsMean μ (bilinearExponent U A B C v w) C| ≤ ε) →
    |Real.log (∫ ω, Real.exp (-(bilinearExponent U A B C 1 1 ω)) ∂μ) +
        Real.log (∫ ω, Real.exp (-(bilinearExponent U A B C 0 0 ω)) ∂μ) -
        Real.log (∫ ω, Real.exp (-(bilinearExponent U A B C 1 0 ω)) ∂μ) -
        Real.log (∫ ω, Real.exp (-(bilinearExponent U A B C 0 1 ω)) ∂μ)| ≤ ε
end YangMills.Construction.MixedDifferences
end
