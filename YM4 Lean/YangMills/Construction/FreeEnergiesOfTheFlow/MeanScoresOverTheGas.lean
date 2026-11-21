import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
def gasMeanScoreProductBound : Prop :=
  WeightedResponses.HoldsAtEveryStep fun T R A => ∀ (n : ℕ) [NeZero n] (G : StepGas.GasGround R n), G.IsAdmissibleGround →
    ∀ (ι : Type) (I : Finset ι) (B : ι → Finset (TorusFields.TorusSite (n * R.params.side))), (∀ i ∈ I, (B i).Nonempty) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j)) →
      WeightedResponses.CaseIntegrable R G.cut G.coarse G.state
        (fun _ Yt ωt _ _ => ∏ i ∈ I, ResponseInTheExpansion.meanSiteScore A.score (B i) Yt ωt) ∧
      Integrable (fun σ => ∏ i ∈ I, gasMeanSiteScore A G (B i) σ) (G.gibbsLaw ∅) ∧
      G.expectation ∅ (fun σ => ∏ i ∈ I, gasMeanSiteScore A G (B i) σ) ≤
        Real.exp (I.card * Real.exp (-(7 * T.gasRate * R.coupling))) *
          ∏ i ∈ I, ResponseInTheExpansion.meanSiteScore (WeightedResponses.coarseLabelScore A.responseParams.s₁ A.score)
            (parentBlocks (B i)) G.state.1 G.state.2
end YangMills.Construction.FreeEnergies
end
