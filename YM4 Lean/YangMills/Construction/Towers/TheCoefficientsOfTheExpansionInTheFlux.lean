import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZero
import YangMills.Construction.Towers.ParametrixOfTheExpansionInTheFlux
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicOperators (castVec)
open InfiniteLattice (AmbientSpace)
namespace Tower.MagneticWeyl
open FluxExpansion in
def FluxCoefficientsAreTrigPolys : Prop :=
  ∀ (N' : ℕ) [NeZero N'] (D C r : ℝ) (σ₁ σ₂ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ)
    (σ σr : ℝ → AmbientSpace → Matrix (Fin N') (Fin N') ℂ), 0 < r →
    (∀ φ : ℝ, |φ| ≤ r →
      IsFiniteFourierSymbol (σ φ) ∧
      (∀ n : Fin 4 → ℤ, D < TorusMetric.euclidNormVec (castVec n) →
        fourierCoeff (σ φ) n = 0) ∧
      (∀ q, σ φ q = baseSymbolMatrix N' q + (φ : ℂ) • σ₁ q + (φ : ℂ) ^ 2 • σ₂ q + σr φ q) ∧
      IsWeylSymbol (σr φ) ∧
      weightedCoeffNorm 3 (σr φ) ≤ C * |φ| ^ 3) →
    IsFiniteFourierSymbol σ₁ ∧ IsFiniteFourierSymbol σ₂ ∧ Continuous σ₁ ∧ Continuous σ₂
end Tower.MagneticWeyl
end YangMills.Construction
end
