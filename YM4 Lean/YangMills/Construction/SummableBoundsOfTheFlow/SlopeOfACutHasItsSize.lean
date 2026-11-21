import YangMills.Construction.SummableBoundsOfTheFlow.LogarithmAlongAMovingCut
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace Estimates
def cutoffSlopeSize : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (n N : ℕ), 0 < ρ → IsCutoff ρ p →
    ∃ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x κ C : ℝ) (Cq₀ : ℕ → ℝ) (d : ι → ι → ℝ)
        (Φ : BondField ι → ℝ) (S : Finset ι) (dZ : ι → ℝ) (e : BondField ι) (E₀ : ℝ),
        1 ≤ x → 0 ≤ E₀ → S.card ≤ n → LawMomentBounds ρ x κ C p Cq₀ Cr d Φ →
        MeasureTheory.Integrable (ballDensity (cutoffFactor ρ p) Φ) →
        (∀ b, b ∉ S → e b = 0) → (∀ b ∈ S, dZ b = 0) → (∀ b, ‖e b‖ ≤ E₀) →
        ContDiffOn ℝ 1 (cutoffSlope p e) {η | ∀ b, ‖η b‖ < ρ} ∧
          HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ (E₀ * (x ^ N)⁻¹) dZ (cutoffSlope p e)
end Estimates
end YangMills.Construction
end
