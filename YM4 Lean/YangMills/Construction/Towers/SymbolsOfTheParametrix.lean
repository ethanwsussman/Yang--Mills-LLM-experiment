import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZero
import YangMills.Construction.Towers.ParametrixOfTheExpansionInTheFlux
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
open PeriodicOperators (castVec)
open FluxExpansion in
def ApproxInverseSymbolBounds : Prop :=
  ∀ (N' : ℕ) [NeZero N'],
    IsFiniteFourierSymbol (baseSymbolMatrix N') ∧
    (∀ n : Fin 4 → ℤ, 1 < TorusMetric.euclidNormVec (castVec n) →
      fourierCoeff (baseSymbolMatrix N') n = 0) ∧
    (∀ μ : Fin 4,
      IsFiniteFourierSymbol (fun q => baseSymbolDeriv μ q • (1 : Matrix (Fin N') (Fin N') ℂ)) ∧
      IsFiniteFourierSymbol (fun q => baseSymbolSecondDeriv μ q • (1 : Matrix (Fin N') (Fin N') ℂ))) ∧
    ∀ z : ℝ, 0 < z → ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, z ≤ s →
      IsWeylSymbol (termZero N' s) ∧ weightedCoeffNorm 3 (termZero N' s) ≤ K / s
end YangMills.Construction.Tower.MagneticWeyl
end
