import YangMills.Construction.ChessboardTori.QuotientMapOnLinksAndPlaquettes
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
def PeriodExpectation.Statement : Prop :=
  ∀ (D : ChessboardSetup) (P : PeriodSubgroup D), P = D.cubicPeriod →
    ∃ Z : ℝ, 0 < Z ∧ ∀ H : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable H →
      D.liftedExpectation H =
        (∫ U, H (P.liftGaugeField U) *
            Complex.exp (-(D.β : ℂ) * (P.wilsonAction U : ℂ)) ∂P.haarMeasure) / (Z : ℂ)
end ChessboardTori
end YangMills.Construction
end
