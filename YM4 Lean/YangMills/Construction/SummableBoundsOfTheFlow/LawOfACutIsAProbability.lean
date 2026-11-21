import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesOfAConvexMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.ConvexObservables
def normalizedBallLawIsProbabilityStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ),
    0 < ρ → IsCutoff ρ p → Continuous Ψ →
    IsProbabilityMeasure (normalizedBallLaw (cutoffFactor ρ p) Ψ) ∧
    (∀ f : BondField ι → ℝ,
      ∫ η, f η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ = ballExpectation (cutoffFactor ρ p) Ψ f) ∧
    (∀ f : BondField ι → ℝ, Integrable f (normalizedBallLaw (cutoffFactor ρ p) Ψ) ↔
      Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η) ∧
    (∀ᵐ η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ, ∀ b, ‖η b‖ < ρ) ∧
    Measurable (ballDensity (cutoffFactor ρ p) Ψ) ∧ (∀ η, 0 ≤ ballDensity (cutoffFactor ρ p) Ψ η) ∧
    Integrable (ballDensity (cutoffFactor ρ p) Ψ) ∧ 0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η ∧
    ContinuousOn (ballDensity (cutoffFactor ρ p) Ψ) {η | ∀ b, ‖η b‖ < ρ} ∧
    (∀ η, ballDensity (cutoffFactor ρ p) Ψ η ≠ 0 ↔ ∀ b, ‖η b‖ < ρ) ∧
    ∀ u v : ℝ, 0 ≤ u → u ≤ v → cutoffFactor ρ p v ≤ cutoffFactor ρ p u
end YangMills.Construction.ConvexObservables
end
