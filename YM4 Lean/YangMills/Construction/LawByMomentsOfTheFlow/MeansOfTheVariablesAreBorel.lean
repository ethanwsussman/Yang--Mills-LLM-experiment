import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def variableMeanAEMeasurableStatement : Prop :=
  ForAllHullParameters fun Λ => ∀ (S : MomentPoint Λ) (u : ℕ), u < S.lastSeparated →
    ∀ J : Finset (Fin Λ.k), J.Nonempty →
    AEMeasurable (variableMean u J S) (S.law S.data.windowLevel (S.data.period Λ.stepParams.side))
end YangMills.Construction.MomentLaw
end
