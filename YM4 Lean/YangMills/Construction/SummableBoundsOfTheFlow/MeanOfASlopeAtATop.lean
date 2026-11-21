import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfTheSlopeAtATop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Cumulants
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Estimates
variable {F : BlockFrame}
def slopeMeanDerivBounds : Prop :=
  ∀ (F : BlockFrame) (s a ρA x : ℝ) (m : ℕ) (ρ κ : ℝ) (p : ℝ → ℝ) (φ : LocalFamily) (V : F.GaugeField F.top)
    (Y : F.Cell) (Hf : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (μ : Measure (StepVariable (finiteCells F))) (b₁ b₂ b₃ b₄ b₅ : ℝ),
    0 < κ → 0 ≤ b₂ → 0 ≤ b₃ → 0 ≤ b₄ →
    GibbsMeanExpansions μ V (interpolatedExponentOfTerms s a ρA x m φ) Hf →
    (∀ f, gibbsMean μ (fun η => interpolatedExponentOfTerms s a ρA x m φ η V) f =
      ballExpectation (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V) f) →
    SlopeCumulantBounds s a ρA x m ρ κ p φ V Y Hf b₂ b₃ b₄ →
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
      |gibbsMean μ (fun η => interpolatedExponentOfTerms s a ρA x m φ η V) (fieldDeriv Hf V c X)| ≤
        b₁ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ)))) →
    (∀ (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
      |ballCovariance (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V)
        (fun η => Hf η V) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c X)| ≤
        b₅ * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ)))) →
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 → AreUnitVectors X →
      |bondDeriv (gibbsMeanAt μ (interpolatedExponentOfTerms s a ρA x m φ) Hf) V c X| ≤
        (b₁ + 3 * b₂ + b₃) * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ)))) ∧
    ∀ (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv (gibbsMeanAt μ (interpolatedExponentOfTerms s a ρA x m φ) Hf) V c X| ≤
        (b₁ + (6 * b₂ + b₅ + 6 * b₃ + b₄)) * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ)))
end YangMills.Construction.Cumulants
end
