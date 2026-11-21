import YangMills.Construction.LawByMomentsOfTheFlow.FunctionsOfTheLimitField
import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.FreeEnergies YangMills.Construction.LevelTestFunctions
def meanScoreProductBoundStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S => ∀ u ≤ S.data.scaleLevel,
    ∀ w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side),
    (∀ i : Fin Λ.k, 1 ≤ meanScoreAtLevel u i S w) ∧ ∀ J : Finset (Fin Λ.k), J.Nonempty →
      ∏ i ∈ J, meanScoreAtLevel u i S w ≤ 1 + 2 ^ J.card * (1 + ∑ z ∈ offsetCube (S.supportRadius u), hullSizePower u z J.card S w)
end YangMills.Construction.MomentLaw
end
