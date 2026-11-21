import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def weightedL1Norm {ι : Type} [Fintype ι] (κ : ℝ) (y : ι → F.Cell) (Y : F.Cell) (ζ : BondField ι) : ℝ :=
  ∑ b, Real.exp (-(2 ^ 4 * κ * cellSupDist (y b) Y)) * ‖ζ b‖
def ObservableSizeOfWeightedBound : Prop :=
  ∀ (κ W : ℝ) (Cq : ℕ → ℝ), 0 ≤ W → (∀ q, 0 ≤ Cq q) → ∃ Cs : ℕ → ℝ, (∀ q, 0 ≤ Cs q) ∧
    ∀ (F : BlockFrame) (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → F.Cell) (ρ l A : ℝ) (p : ℝ → ℝ)
      (Ψ : BondField ι → ℝ) (Y : F.Cell) (H : BondField ι → ℝ),
      0 < ρ → 0 < l → 0 ≤ A → IsCutoff ρ p → Continuous Ψ →
      (∑ b, Real.exp (-(2 ^ 4 * κ * cellSupDist (y b) Y)) ≤ W) →
      (∀ (q : ℕ) (b : ι), ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ Cq q * ((l⁻¹ ^ 2) ^ q)⁻¹) →
      ContDiffOn ℝ 1 H {ζ | ∀ b, l * ‖ζ b‖ < ρ} →
      (∀ ζ : BondField ι, (∀ b, l * ‖ζ b‖ < ρ) → |H ζ| ≤ A * (1 + weightedL1Norm κ y Y ζ) ^ 7) →
      (∀ (ζ : BondField ι) (b : ι) (e : BondVector), (∀ b, l * ‖ζ b‖ < ρ) → ‖e‖ = 1 →
        |bondPartialDeriv H b ζ e| ≤ A * Real.exp (-(2 * κ * cellSupDist (y b) Y)) * (1 + weightedL1Norm κ y Y ζ) ^ 7) →
      (∀ q : ℕ, 1 ≤ q → MomentBound (cutoffFactor ρ p) Ψ (fun η => H (l⁻¹ • η)) q (Cs q * A)) ∧
        HasLocalSize ρ (cutoffFactor ρ p) Ψ Cs (l⁻¹ ^ 2) κ A (fun b => (cellSupDist (y b) Y : ℝ)) fun η => H (l⁻¹ • η)
end YangMills.Construction.Interpolation
end
