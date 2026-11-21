import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import YangMills.Construction.SummableBoundsOfTheFlow.RadialSlopeOfACut
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.Estimates
open ColdStepAtMirrorFrames Interpolation
def localSizeOfCutoffDerivBoundStatement : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (n N : ℕ) (K : ℝ), 0 < ρ → 0 ≤ K →
    ∃ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x κ h : ℝ) (Φ : BondField ι → ℝ) (S : Finset ι)
        (dZ : ι → ℝ) (H : BondField ι → ℝ),
        1 ≤ x → 0 ≤ h → S.card ≤ n →
        AEStronglyMeasurable (ballDensity (cutoffFactor ρ p) Φ) volume →
        (∀ (j q N' : ℕ) (b : ι), 1 ≤ j → 1 ≤ q →
          Integrable (fun η => |iteratedDeriv j p ‖η b‖| ^ q * ballDensity (cutoffFactor ρ p) Φ η) ∧
          ballExpectation (cutoffFactor ρ p) Φ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) ≤ Cr j q N' * (x ^ N')⁻¹) →
        (∀ b ∈ S, dZ b = 0) →
        DifferentiableOn ℝ H {η | ∀ b, ‖η b‖ < ρ} →
        (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H η| ≤ K * h * ∑ b ∈ S, cutoffDerivSum p ‖η b‖) →
        (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm H b η ≤
          if b ∈ S then K * h * ∑ b ∈ S, cutoffDerivSum p ‖η b‖ else 0) →
        HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ (h * (x ^ N)⁻¹) dZ H
end YangMills.Construction.Estimates
end
