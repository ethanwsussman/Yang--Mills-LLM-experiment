import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open WeightedResponses StepGas RenormalizationStepParameters TorusFields TorusLumps BlockAverages
def productMeanScoreStepBound : Prop :=
  HoldsAtEveryStep fun T R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (ι : Type) (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side))), (∀ i ∈ I, (B i).Nonempty) →
      CaseIntegrable R G.cut G.coarse G.state (fun _ Yt ωt _ _ => ∏ i ∈ I, meanSiteScore A.score (B i) Yt ωt) ∧
      caseMean R G.cut G.coarse G.state (fun _ Yt ωt _ _ => ∏ i ∈ I, meanSiteScore A.score (B i) Yt ωt) ≤
        Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling))) *
          ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
            (open Classical in (B i).image (parentBlock R.params.side)) G.state.1 G.state.2
end ResponseInTheExpansion
end YangMills.Construction
end
