import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace FreeEnergies
open StepSettings TorusFields TorusLumps WeightedResponses ResponseInTheExpansion
variable {R : StepSetup} {n : ℕ} [NeZero n]
def parentBlocks (S : Finset (TorusSite (n * R.params.side))) : Finset (TorusSite n) :=
  open Classical in S.image (parentBlock R.params.side)
def scoreSumOn (A : ResponseSetup R) (S : Finset (TorusSite (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) : ℝ :=
  ∑ y ∈ S, siteScore A.score Yt ωt y
def coarseSiteScore (A : ResponseSetup R) (q : CoarseState R n) (Y : TorusSite n) : ℝ :=
  siteScore (coarseLabelScore A.responseParams.s₁ A.score) q.1 q.2 Y
def prodMeanSiteScores (A : ResponseSetup R) {p : ℕ} (B : Fin p → Finset (TorusSite (n * R.params.side))) :
    CaseFunction R n :=
  fun _ Yt ωt _ _ => ∏ i, meanSiteScore A.score (B i) Yt ωt
end FreeEnergies
end YangMills.Construction
end
