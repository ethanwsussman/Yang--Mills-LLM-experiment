import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZero
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (torusAverage toComplexVec)
noncomputable section
namespace YangMills.Construction.Tower.ConstantSymbols
open MagneticWeyl Massive
def MassiveStiffnessFormula : Prop :=
  ∃ σ₁ σ₂ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ,
    IsFiniteFourierSymbol σ₁ ∧ IsFiniteFourierSymbol σ₂ ∧
    (∀ q, (σ₁ q).IsHermitian) ∧ (∀ q, (σ₂ q).IsHermitian) ∧
    ((σ₁ 0) ^ 2).trace = 8 ∧
    ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ hL : 0 < L, ∀ z : ℝ, 0 < z →
      MassiveStiffnessExists hL z ∧
      (massiveStiffness hL z : ℂ) =
        8 * torusAverage (fun q =>
          1 / 2 * resolvent z (toComplexVec q) ^ 2 * ((σ₁ q) ^ 2).trace -
            1 / 12 * resolvent z (toComplexVec q) ^ 2 *
                partialIn 0 (partialIn 0 latticeSymbol) (toComplexVec q) *
                partialIn 1 (partialIn 1 latticeSymbol) (toComplexVec q) -
              resolvent z (toComplexVec q) * (σ₂ q).trace) +
          1 / 2 * torusAverage (fun q =>
            resolvent z (toComplexVec q) *
              (axisSymbol 0 (toComplexVec q) + axisSymbol 1 (toComplexVec q)))
end YangMills.Construction.Tower.ConstantSymbols
end
