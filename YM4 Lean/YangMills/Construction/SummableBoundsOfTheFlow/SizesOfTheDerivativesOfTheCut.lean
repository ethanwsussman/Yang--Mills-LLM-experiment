import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory ColdStepAtMirrorFrames
namespace Interpolation
def cutoffDerivSizesStatement : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (j : ℕ), 0 < ρ → IsCutoff ρ p → 1 ≤ j → (∀ j q N, 0 ≤ Cr j q N) →
    ∃ Cs : ℕ → ℝ, (∀ q, 0 ≤ Cs q) ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b₀ : ι) (l κ : ℝ) (Ψ : BondField ι → ℝ) (dZ : ι → ℝ),
        0 < l → l ≤ 1 → Continuous Ψ → dZ b₀ = 0 →
        (∀ (j q N : ℕ) (b : ι), 1 ≤ j → 1 ≤ q →
          Integrable (fun η => |iteratedDeriv j p ‖η b‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) ∧
          ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) ≤ Cr j q N * ((l⁻¹ ^ 2) ^ N)⁻¹) →
        ContDiffOn ℝ 1 (fun η : BondField ι => ‖(l⁻¹ • η) b₀‖ ^ j * iteratedDeriv j p (l * ‖(l⁻¹ • η) b₀‖))
          {η | ∀ b, ‖η b‖ < ρ} ∧
        (∀ q : ℕ, 1 ≤ q → MomentBound (cutoffFactor ρ p) Ψ
          (fun η => ‖(l⁻¹ • η) b₀‖ ^ j * iteratedDeriv j p (l * ‖(l⁻¹ • η) b₀‖)) q (Cs q * 1)) ∧
        HasLocalSize ρ (cutoffFactor ρ p) Ψ Cs (l⁻¹ ^ 2) κ 1 dZ
          fun η => ‖(l⁻¹ • η) b₀‖ ^ j * iteratedDeriv j p (l * ‖(l⁻¹ • η) b₀‖)
end Interpolation
end YangMills.Construction
end
