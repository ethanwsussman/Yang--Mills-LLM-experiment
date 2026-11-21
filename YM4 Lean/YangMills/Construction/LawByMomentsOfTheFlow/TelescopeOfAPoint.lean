import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def telescopeIdentityStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S =>
    (∀ (i : Fin Λ.k) (n : ℕ) (hn : n ≤ S.data.windowLevel),
      ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
        WeightedResponses.completedObservable S.tower S.coeff n (S.sideAtLevel n) (S.weight i _)
            (S.sampleAtLevel n hn w) - S.kappa n (S.sideAtLevel n) i =
          responseAtLevel 0 i S w + ∑ j ∈ Finset.range n, centredStepScore j i S w) ∧
    ∀ u : ℕ, u < S.data.windowLevel → ∀ J : Finset (Fin Λ.k),
      ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)),
        variableProduct u J S w = ∏ i ∈ J, (responseAtLevel u i S w + centredStepScore u i S w)
end YangMills.Construction.MomentLaw
end
