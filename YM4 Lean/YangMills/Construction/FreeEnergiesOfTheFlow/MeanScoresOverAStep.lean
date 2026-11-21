import YangMills.Construction.FreeEnergiesOfTheFlow.ScoresOverAStepDefs
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace FreeEnergies
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
def meanSiteScoresStepBound : Prop :=
  HoldsAtEveryStep fun T R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (p : ℕ) (B : Fin p → Finset (TorusSite (n * R.params.side))), (∀ i, (B i).Nonempty) →
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
      CaseIntegrable R G.cut G.coarse G.state (prodMeanSiteScores A B) ∧
      caseMean R G.cut G.coarse G.state (prodMeanSiteScores A B) ≤
        Real.exp (p * Real.exp (-(7 * T.gasRate * R.coupling))) *
          ∏ i, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks (B i)) G.state.1 G.state.2
end FreeEnergies
end YangMills.Construction
end
