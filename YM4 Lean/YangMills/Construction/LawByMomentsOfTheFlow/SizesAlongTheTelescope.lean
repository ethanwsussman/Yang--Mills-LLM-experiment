import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.FreeEnergies YangMills.Construction.LevelTestFunctions
def telescopeTermBoundsStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S =>
    (∀ u < S.data.scaleLevel, ∀ (i : Fin Λ.k)
        (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)),
      |centredStepScore u i S w| ≤ 2 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ))) ∧
    ∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k, ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
      |responseAtLevel u i S w| ≤
        Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) * meanScoreAtLevel u i S w
end YangMills.Construction.MomentLaw
end
