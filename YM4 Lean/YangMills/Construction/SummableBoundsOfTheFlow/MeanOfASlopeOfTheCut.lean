import YangMills.Construction.SummableBoundsOfTheFlow.LogarithmAlongAMovingCut
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Estimates
open BlockAverages ColdStepAtMirrorFrames
def cutoffSlopeMeanBoundStatement : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (n N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (x κ C : ℝ) (Cq₀ : ℕ → ℝ) (d : ι → ι → ℝ) (Φ : BondField ι → ℝ) (S : Finset ι) (e : BondField ι)
    (E₀ : ℝ),
    0 ≤ E₀ → 0 < x → S.card ≤ n → Interpolation.LawMomentBounds ρ x κ C p Cq₀ Cr d Φ →
    (∀ b, b ∉ S → e b = 0) → (∀ b, ‖e b‖ ≤ E₀) →
    |ballExpectation (cutoffFactor ρ p) Φ (cutoffSlope p e)| ≤ n * |Cr 1 1 N| * (E₀ * (x ^ N)⁻¹)
end YangMills.Construction.Estimates
end
