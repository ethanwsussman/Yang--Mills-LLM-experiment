import YangMills.Construction.Matrices.SecondDifferentialOfTheLogarithmOfADeterminant
import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveLogDet
open YangMills.Construction.Coordinates
open YangMills.Construction.PeriodicOperators (toComplexVec)
open YangMills.Construction.PeriodicOperators.Tempered (hessianSymbol)
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
def SymbolHolomorphy : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ μ ν : Fin 4, ∀ z₀ : ℝ, 0 < z₀ →
    ∀ p₀ : InfiniteLattice.AmbientSpace, ∃ O : Set (ComplexCoordinates 5),
      (∃ w₀ ∈ O, w₀ 0 = (z₀ : ℂ) ∧ ∀ i : Fin 4, w₀ i.succ = toComplexVec p₀ i) ∧
        ∃ H : ComplexCoordinates 5 → ℂ, IsHolomorphicScalarIn O H ∧
          ∀ w ∈ O, w ∈ ComplexCoordinates.realLocus 5 → 0 < (w 0).re →
            H w = hessianSymbol L (massiveFieldFamily L (w 0).re) μ ν fun i => w i.succ
end YangMills.Construction.Tower.MassiveLogDet
end
