import YangMills.Construction.ResponseInTheExpansion.ALocalFunctionIsQuadraticInTheCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open RenormalizationStepParameters TorusFields StepCosts
open Classical
open MeasureTheory
def shareCurvatureFormAt (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ C₂ c₂ D₂ d₂ : ℝ, 0 < c₂ → 0 < d₂ → ∃ C₃ c₃ ρ₁ : ℝ, 0 < c₃ ∧
    ∀ (k n : ℕ) [NeZero n] (ρ₀ : ℝ) (z : TorusSite n) (κ : TorusPlaquette n → TorusPlaquette n → ℝ),
    ρ₁ ≤ ρ₀ → Tb.n₀ ≤ n → 2 * ρ₀ + 2 < n →
    (∀ p p', κ p p' = κ p' p) →
    (∀ p p', ρ₀ < (supDist p.1 z : ℝ) ∨ ρ₀ < (supDist p'.1 z : ℝ) → κ p p' = 0) →
    (∀ p p', |κ p p'| ≤ D₂ * Real.exp (-(d₂ * max (supDist p.1 z : ℝ) (supDist p'.1 z : ℝ)))) →
    IsQuadraticInCurvature (Tb.stepParameters y).threshold C₂ c₂ 1 ρ₀
      (levelShare Tb.coupling (Tb.stepParameters y).side k Finset.univ z) z κ →
    ∀ μ ν ρ τ : Fin 4, μ < ν → ρ < τ →
      |∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette n => p.2 = (μ, ν)),
        ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette n => p'.2 = (ρ, τ)), κ p p' -
        (if (μ, ν) = (ρ, τ) then 1 else 0)| ≤ C₃ * Real.exp (-(c₃ * ρ₀))
def shareCurvatureFormStatement : Prop := HoldsOnParameterFamilies shareCurvatureFormAt
end YangMills.Construction.ResponseInTheExpansion
end
