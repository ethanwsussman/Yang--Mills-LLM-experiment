import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
def FiniteSumSizeBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : Type) (S : Finset J) (ρ x κ B : ℝ) (p : ℝ → ℝ)
    (Ψ : ColdStepAtMirrorFrames.BondField ι → ℝ) (C : ℕ → ℝ)
    (H : J → ColdStepAtMirrorFrames.BondField ι → ℝ) (w : J → ℝ)
    (d : J → ι → ℝ) (d₀ : ι → ℝ), 0 < ρ → ColdStepAtMirrorFrames.IsCutoff ρ p → Continuous Ψ → 0 < x →
    (∀ q, 0 < C q) →
    (∀ j, 0 < w j) → (∀ j, ContDiffOn ℝ 1 (H j) {η | ∀ b, ‖η b‖ < ρ}) →
    (∀ j ∈ S, Interpolation.HasLocalSize ρ (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ C x κ (w j) (d j) (H j)) →
    ∑ j ∈ S, w j ≤ B →
    (∀ b, ∑ j ∈ S, w j * Real.exp (-(2 * κ * d j b)) ≤ B * Real.exp (-(2 * κ * d₀ b))) →
    Interpolation.HasLocalSize ρ (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ C x κ B d₀
      fun η => ∑ j ∈ S, H j η
end YangMills.Construction.WeightedResponses
end
