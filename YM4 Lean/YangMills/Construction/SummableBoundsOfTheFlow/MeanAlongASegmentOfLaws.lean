import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.DensityMeans
def weightedMean {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w Ψ H : Ω → ℝ) : ℝ :=
  (∫ ω, H ω * (w ω * Real.exp (- Ψ ω)) ∂μ) / ∫ ω, w ω * Real.exp (- Ψ ω) ∂μ
def segmentPoint {Ω : Type} (f₀ f₁ : Ω → ℝ) (v : ℝ) (ω : Ω) : ℝ := v * f₁ ω + (1 - v) * f₀ ω
def meanDerivAlongSegment {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (w Ψ₀ Ψ₁ A₀ A₁ : Ω → ℝ) (v : ℝ) : ℝ :=
  weightedMean μ w (segmentPoint Ψ₀ Ψ₁ v) (fun ω => A₁ ω - A₀ ω) -
    (weightedMean μ w (segmentPoint Ψ₀ Ψ₁ v) (fun ω => segmentPoint A₀ A₁ v ω * (Ψ₁ ω - Ψ₀ ω)) -
      weightedMean μ w (segmentPoint Ψ₀ Ψ₁ v) (segmentPoint A₀ A₁ v) *
        weightedMean μ w (segmentPoint Ψ₀ Ψ₁ v) (fun ω => Ψ₁ ω - Ψ₀ ω))
def WeightedMeanDiffLeOfDerivBound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) (w Ψ₀ Ψ₁ A₀ A₁ : Ω → ℝ) (M B : ℝ),
    MeasurableSet S → (∀ ω, 0 ≤ w ω) → (∀ ω, ω ∉ S → w ω = 0) → Integrable w μ →
    0 < ∫ ω, w ω ∂μ → AEStronglyMeasurable Ψ₀ (μ.restrict S) →
    AEStronglyMeasurable Ψ₁ (μ.restrict S) → (∀ ω ∈ S, |Ψ₀ ω| ≤ M) → (∀ ω ∈ S, |Ψ₁ ω| ≤ M) →
    Integrable (fun ω => A₀ ω * w ω) μ → Integrable (fun ω => A₁ ω * w ω) μ →
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 → |meanDerivAlongSegment μ w Ψ₀ Ψ₁ A₀ A₁ v| ≤ B) →
    |weightedMean μ w Ψ₁ A₁ - weightedMean μ w Ψ₀ A₀| ≤ B
end YangMills.Construction.DensityMeans
end
