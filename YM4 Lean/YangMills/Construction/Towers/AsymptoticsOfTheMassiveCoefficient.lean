import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZero
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.Massive
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage toComplexVec)
open MagneticWeyl
def MassiveCoefficientAsymptotics : Prop :=
  ∀ σ₁ σ₂ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ,
    IsFiniteFourierSymbol σ₁ → IsFiniteFourierSymbol σ₂ → ((σ₁ 0) ^ 2).trace = 8 →
    ∀ β : ℝ → ℝ,
      (∀ z : ℝ, 0 < z → (β z : ℂ) =
        8 * torusAverage (fun q =>
          1 / 2 * resolvent z (toComplexVec q) ^ 2 * ((σ₁ q) ^ 2).trace -
            1 / 12 * resolvent z (toComplexVec q) ^ 2 *
                partialIn 0 (partialIn 0 latticeSymbol) (toComplexVec q) *
                partialIn 1 (partialIn 1 latticeSymbol) (toComplexVec q) -
              resolvent z (toComplexVec q) * (σ₂ q).trace) +
          1 / 2 * torusAverage (fun q =>
            resolvent z (toComplexVec q) *
              (axisSymbol 0 (toComplexVec q) + axisSymbol 1 (toComplexVec q)))) →
      ContDiffOn ℝ 2 β (Set.Ioi 0) ∧
        ∃ C : ℝ, ∀ z : ℝ, 0 < z → z ≤ 1 →
          |β z - 11 / (6 * Real.pi ^ 2) * Real.log (1 / z)| + |z * deriv β z| +
            |z ^ 2 * deriv (deriv β) z| ≤ C
end YangMills.Construction.Tower.Massive
end
