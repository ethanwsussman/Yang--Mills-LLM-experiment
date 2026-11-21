import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ByPartsAtABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.BondIntegration
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def radialCutoffSlope (p : ℝ → ℝ) (v e : BondVector) : ℝ := deriv p ‖v‖ * ‖v‖⁻¹ * ⟪v, e⟫
def fieldDerivative (b : ι) (z : BondVector → BondVector) (H : BondField ι → ℝ) (η : BondField ι) : ℝ :=
  bondPartialDeriv H b η (z (η b))
def fieldScore (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (b : ι) (z : BondVector → BondVector)
    (η : BondField ι) : ℝ :=
  bondPartialDeriv Ψ b η (z (η b)) + radialCutoffSlope p (η b) (z (η b)) - bondDivergence z (η b)
structure DensityProductVanishesAtBoundary (ρ : ℝ) (p : ℝ → ℝ) (Ψ G : BondField ι → ℝ) : Prop where
  differentiable : Differentiable ℝ fun η => G η * ballDensity (cutoffFactor ρ p) Ψ η
  fderiv_eq_zero_outside : ∀ η : BondField ι, ¬ (∀ b, ‖η b‖ < ρ) →
    fderiv ℝ (fun ζ => G ζ * ballDensity (cutoffFactor ρ p) Ψ ζ) η = 0
def integralAlongFieldStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : ℝ) (p : ℝ → ℝ) (Ψ G : BondField ι → ℝ) (b : ι)
    (z : BondVector → BondVector) (C : ℝ), 0 < ρ → IsCutoff ρ p →
    ContDiffOn ℝ 1 Ψ {η | ∀ b, ‖η b‖ < ρ} → ContDiffOn ℝ 1 G {η | ∀ b, ‖η b‖ < ρ} →
    ContDiff ℝ 1 z → (∀ v, ‖z v‖ ≤ C) → (∀ v, ‖fderiv ℝ z v‖ ≤ C) →
    DensityProductVanishesAtBoundary ρ p Ψ G →
    Integrable (fun η => G η * ballDensity (cutoffFactor ρ p) Ψ η) →
    (∀ e : BondVector, Integrable fun η =>
      fderiv ℝ (fun ζ => G ζ * ballDensity (cutoffFactor ρ p) Ψ ζ) η (bondVariation b e)) →
    Integrable (fun η => fieldDerivative b z G η * ballDensity (cutoffFactor ρ p) Ψ η) →
    Integrable (fun η => G η * fieldScore p Ψ b z η * ballDensity (cutoffFactor ρ p) Ψ η) →
    ∫ η, fieldDerivative b z G η * ballDensity (cutoffFactor ρ p) Ψ η =
      ∫ η, G η * fieldScore p Ψ b z η * ballDensity (cutoffFactor ρ p) Ψ η
end YangMills.Construction.BondIntegration
end
