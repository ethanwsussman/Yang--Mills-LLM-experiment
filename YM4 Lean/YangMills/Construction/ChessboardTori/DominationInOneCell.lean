import YangMills.Construction.ChessboardTori.LimitingChessboardSeminorm
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
def CellDomination.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    ∀ F : D.GaugeField → ℂ, F ∈ ReflectionGrid.cellObservables (D := D) g.baseCell →
      (∀ μ : Measure D.GaugeField, InfiniteLattice.IsGibbs D.β μ →
        (∀ r : g.reflectionGroup, InfiniteLattice.IsSymmetricUnder μ (g.toLatticeSym r)) →
        ‖∫ U, F U ∂μ‖ ≤ g.limChessboardNorm F) ∧
      ∀ μ ∈ D.periodicStates, ‖∫ U, F U ∂μ‖ ≤ g.limChessboardNorm F
end ChessboardTori
end YangMills.Construction
end
