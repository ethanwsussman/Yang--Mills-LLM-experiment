import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
def stepMajorantBoundOfSymmetric : Prop :=
  WeightedResponses.HoldsAtEveryStep fun T R A => R.IsSymmetricWeight →
    ∀ (h : ClusterExpansionOfAStep.CoarseLabelFacts R) (x'' : ℝ) (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide R.params n →
    ∀ (ι : Type) (I : Finset ι) (B : ι → Finset (TorusFields.TorusSite (n * R.params.side))), (∀ i ∈ I, (B i).Nonempty) →
      stateLIntegral R (n * R.params.side) (fun _ Y ω => ∏ i ∈ I, meanSiteScore A.score (B i) Y ω) ≤
        ENNReal.ofReal (Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling)))) *
          stateLIntegral (nextStepSetup R h T.lam x'') n (fun _ Y ω => ∏ i ∈ I,
            meanSiteScore (WeightedResponses.coarseLabelScore A.responseParams.s₁ A.score)
              (open Classical in (B i).image (TorusLumps.parentBlock R.params.side)) Y ω)
end YangMills.Construction.ResponseInTheExpansion
end
