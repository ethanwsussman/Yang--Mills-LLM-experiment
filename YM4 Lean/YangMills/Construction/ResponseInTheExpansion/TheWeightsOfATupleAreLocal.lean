import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def testWeightsLocalStatement : Prop :=
  ∀ (P : YangMills.Construction.TorusLumps.StepParameters), Odd P.side → ∀ (m k q : ℕ) (n vt : ℝ)
    (f : Fin (q + 1) → YangMills.Construction.PeriodicLattice.FourTorus P.side m → ℝ),
    1 ≤ n → 0 < vt → IsSeparatedTestTuple P m n vt f →
    (∀ i, YangMills.Construction.WeightedResponses.weightSup
        (YangMills.Construction.WeightedResponses.testWeight P.side k m (f i)) ≤ 1) ∧
    (∀ i, YangMills.Construction.WeightedResponses.weightLipschitz P.side k
        (YangMills.Construction.WeightedResponses.testWeight P.side k m (f i)) ≤ 2 / (vt * n)) ∧
    ∃ o : YangMills.Construction.TorusFields.TorusSite (2 * P.side ^ m),
      ∀ (i : Fin (q + 1)) (z : YangMills.Construction.TorusFields.TorusSite (2 * P.side ^ m))
        (p : YangMills.Construction.TorusFields.TorusPlaquette
          (YangMills.Construction.WeightedResponses.fineSide P.side k (2 * P.side ^ m))),
      z ∉ supBall o (12 * n) → YangMills.Construction.WeightedResponses.IsPlaquetteAt P.side k z p →
        YangMills.Construction.WeightedResponses.testWeight P.side k m (f i) p = 0
end YangMills.Construction.ResponseInTheExpansion
end
