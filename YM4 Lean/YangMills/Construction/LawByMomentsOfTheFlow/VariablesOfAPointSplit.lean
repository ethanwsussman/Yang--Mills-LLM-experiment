import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.FreeEnergies YangMills.Construction.LevelTestFunctions
def stepVariableMeanSplitStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ u < S.lastSeparated, ∀ J : Finset (Fin Λ.k), J.Nonempty → ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
    |variableMean u J S w - ∏ i ∈ J, responseAtLevel (u + 1) i S w| ≤
      S.stepErrorBound (C 0) u J * ∏ i ∈ J, meanScoreAtLevel (u + 1) i S w
end YangMills.Construction.MomentLaw
end
