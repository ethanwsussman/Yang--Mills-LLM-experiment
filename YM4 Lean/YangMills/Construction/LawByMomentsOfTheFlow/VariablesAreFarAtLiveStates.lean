import YangMills.Construction.LawByMomentsOfTheFlow.FarCopiesInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
def stepVariablesQuasiLocalStatement : Prop :=
  ForAllHullParameters fun P => ∀ (S : MomentPoint P) (u : ℕ), u < S.data.scaleLevel →
    ∀ J : Finset (Fin P.k), ∃ (Rr : ℕ) (Sz C : ℝ),
    ∀ S' : MomentPoint P, (∃ m hp hs, S' = S.withSideExponent m hp hs) →
      ∃ A : Finset (TorusFields.TorusSite (S'.sideAtLevel (u + 1) * P.stepParams.side)),
      (∀ V, IsQuasiLocalCaseFunction (S'.tower.stage u).toStepSetup (S'.originSite u _) Rr J.card Sz A
        (S'.resp u).score (S'.variableCaseProduct u J V)) ∧
      Measurable (FreeEnergies.caseLift S'.tower u _ (S'.variableCaseProduct u J)) ∧
      (∀ᵐ x ∂(WeightedResponses.markedSampleLaw S'.tower S'.β (u + 1) (S'.sideAtLevel (u + 1))),
        FreeEnergies.CaseIntegrableAtSample S'.tower u _ (S'.variableCaseProduct u J) x) ∧
      ∫⁻ x, ENNReal.ofReal (supportWeightOfSample S'.tower u _ A (S'.resp u).score x)
        ∂(WeightedResponses.markedSampleLaw S'.tower S'.β (u + 1) (S'.sideAtLevel (u + 1))) ≤ ENNReal.ofReal C
end YangMills.Construction.MomentLaw
end
