import YangMills.Construction.Towers.SecondOrderInTheFlux
import YangMills.Construction.Towers.SymbolsOfTheConstantField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
def NeutralLogSecondOrder : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z → ∃ C : ℝ, ∀ f : ℝ, |f| ≤ 1 →
    ‖Tower.MagneticWeyl.FluxSecondOrder.logTrace L z 0 (neutralSectorSymbol f) -
        (Tower.MagneticWeyl.FluxSecondOrder.constantTerm 4 z - (f : ℂ) ^ 2 / 2 *
          PeriodicOperators.torusAverage fun q =>
            Tower.Massive.resolvent z (PeriodicOperators.toComplexVec q) *
              (Tower.Massive.axisSymbol 0 (PeriodicOperators.toComplexVec q) +
                Tower.Massive.axisSymbol 1 (PeriodicOperators.toComplexVec q)))‖ ≤
      C * f ^ 4
end YangMills.Construction.Tower.ConstantFieldSymbols
end
