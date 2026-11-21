import YangMills.Construction.ResponseInTheExpansion.SymbolOfTheMaxwellForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open LinearResponse TorusFields
open Classical
open MeasureTheory
structure IsLowMomentumSymbol (B : ℕ → ℝ) (C c ε : ℝ) (S : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop where
  smooth : ∀ (r : ℕ) (μ ν : Fin 4), ContDiff ℝ r fun p => S p μ ν
  periodic_shift : ∀ (p : Fin 4 → ℝ) (i μ ν : Fin 4),
    S (p + Pi.single i (2 * Real.pi)) μ ν = periodShiftSign i μ ν * S p μ ν
  deriv_le : ∀ (r : ℕ) (μ ν : Fin 4) (p : Fin 4 → ℝ), ‖iteratedFDeriv ℝ r (fun p => S p μ ν) p‖ ≤ B r
  near_transverse : ∀ (p : Fin 4 → ℝ) (μ ν : Fin 4),
    ‖S p μ ν - ((sqNorm p * (if μ = ν then 1 else 0) - p μ * p ν : ℝ) : ℂ)‖ ≤ C * (sqNorm p ^ 2 + ε)
  coercive : ∀ (p : Fin 4 → ℝ) (v : Fin 4 → ℂ),
    c * sqNorm (latticeMomentum p) * ∑ m, ‖v m‖ ^ 2 - C * ε * ∑ m, ‖v m‖ ^ 2 ≤
      (∑ m, ∑ m', (starRingEnd ℂ) (v m) * symbolWithGradient S p m m' * v m').re
def lowSymbolKernelStatement : Prop :=
  ∀ (B : ℕ → ℝ) (C c c' : ℝ), 0 < c → 0 < c' → ∃ C' N₀ : ℝ, ∀ (N : ℕ) [NeZero N] (ε : ℝ)
    (S : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (μ ν ρ τ : Fin 4) (z : Fin 4 → ℝ), N₀ ≤ N → 0 ≤ ε → ε ≤ Real.exp (-(c' * (N : ℝ))) →
    IsLowMomentumSymbol B C c ε S →
    μ < ν → ρ < τ →
    (∀ i, ∃ w : ℤ, z i = w + ((if i = ρ then 1 else 0) + (if i = τ then 1 else 0) - (if i = μ then 1 else 0) -
      (if i = ν then 1 else 0)) / 2) → 1 ≤ sqNorm z → sqNorm z ≤ ((N : ℝ) / 8) ^ 2 →
    ‖inverseSymbolFourierSum N S μ ν ρ τ z - (continuumCurvatureKernel z μ ν ρ τ : ℂ)‖ ≤
      C' * (sqNorm z ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ)))
end YangMills.Construction.ResponseInTheExpansion
end
