import YangMills.Construction.ResponseInTheExpansion.SumOverMomentaOfASymbolOfOrderOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
namespace ResponseInTheExpansion
open Classical
open scoped ContDiff
def planeCurl (p : Fin 4 → ℝ) (μ ν m : Fin 4) : ℂ :=
  Complex.I * (((if m = ν then p μ else 0) - (if m = μ then p ν else 0) : ℝ) : ℂ)
def doubleCurlSymbol (μ ν ρ τ : Fin 4) (p : Fin 4 → ℝ) : ℂ :=
  (∑ m, (starRingEnd ℂ) (planeCurl p μ ν m) * planeCurl p ρ τ m) / (LinearResponse.sqNorm p : ℂ)
def curlCurlMomentumSumStatement : Prop :=
  ∀ χ : (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ χ → (∀ᶠ p in nhds 0, χ p = 1) →
    (∀ p, 1 ≤ LinearResponse.sqNorm p → χ p = 0) →
    ∃ C N₀ : ℝ, ∀ (N : ℕ) [NeZero N] (μ ν ρ τ : Fin 4) (z : Fin 4 → ℝ), N₀ ≤ N → μ < ν → ρ < τ →
      1 ≤ LinearResponse.sqNorm z → LinearResponse.sqNorm z ≤ ((N : ℝ) / 8) ^ 2 →
      ‖ResponseInTheExpansion.nonzeroMomentumWave N (fun p => (χ p : ℂ) * doubleCurlSymbol μ ν ρ τ p) z -
          (LinearResponse.continuumCurvatureKernel z μ ν ρ τ : ℂ)‖ ≤
        C * (LinearResponse.sqNorm z ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ)))
end ResponseInTheExpansion
end YangMills.Construction
end
