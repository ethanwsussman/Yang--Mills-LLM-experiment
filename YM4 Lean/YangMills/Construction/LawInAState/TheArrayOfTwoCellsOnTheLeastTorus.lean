import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.LawInAState
def twoCellPeriodicMeanStatement : Prop :=
  ∀ (S : YangMills.Construction.ChessboardTori.ChessboardSetup)
    (G : YangMills.Construction.ChessboardTori.ReflectionGrid S), G.q = 0 →
    ∀ F : S.GaugeField → ℂ, Measurable F → (∃ M : ℝ, ∀ U, ‖F U‖ ≤ M) →
    (∫ U, F ((YangMills.Construction.ReflectedCopies.gridPeriods G
          (YangMills.Construction.ReflectedCopies.minimalCounts S)).liftGaugeField U) *
        Complex.exp (-(S.β : ℂ) * ((YangMills.Construction.ReflectedCopies.gridPeriods G
          (YangMills.Construction.ReflectedCopies.minimalCounts S)).wilsonAction U : ℂ))
        ∂(YangMills.Construction.ReflectedCopies.gridPeriods G
          (YangMills.Construction.ReflectedCopies.minimalCounts S)).haarMeasure) /
        (YangMills.Construction.ReflectedCopies.torusPartition G
          (YangMills.Construction.ReflectedCopies.minimalCounts S) : ℂ) =
      ∫ U, F U ∂YangMills.Construction.StateLaws.unitTorusMeasure S.L S.K S.β
end YangMills.Construction.LawInAState
end
