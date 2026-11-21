import YangMills.Construction.Towers.TheSymbolOfOneStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseCoefficients
open YangMills.Construction
def ColourCoefficientClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ (κ : Fin 4 → ℂ) (ρ μ : Fin 4)
    (m : Fin 4 → ℤ) (a : Fin 3) (z : (PeriodicOperators.colourEdges L k k).UnitQuot → ℂ),
    PeriodicOperators.SymbolSummableAt (PeriodicOperators.colourEdges L k k)
      (PeriodicOperators.colourEdges L k 0) (Tower.BackgroundFieldResponse.responseKernel L k) κ →
    (∀ ν, Tower.PlaneWaveCalculus.topEdgeComponent L k z ν =
        if ν = μ then Matrices.ComplexMatrix2.pauliFamily a else 0) →
      Tower.PlaneWaves.edgeFourierCoeff L k (Tower.ResponseProperties.responseSymbolForm L k κ z) ρ m =
        PeriodicOperators.Tempered.OneStep.responseCoeff L k κ ρ μ m • Matrices.ComplexMatrix2.pauliFamily a
end YangMills.Construction.Tower.ResponseCoefficients
end
