import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.StepSettings YangMills.Construction.StepGas YangMills.Construction.BlockAverages
section SupportMoments
variable {n : ℕ} [NeZero n]
def meanSiteScore {Ω : Type} (s : Ω → ℝ) (B Y : Finset (TorusSite n)) (ω : Y → Ω) : ℝ :=
  1 + (B.card : ℝ)⁻¹ * ∑ y ∈ B, siteScore s Y ω y
open Classical in
def weightSupportSites (L t : ℕ) [NeZero L] (n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide L t n)) :
    Finset (TorusSite n) :=
  Finset.univ.filter fun y => ∃ p, IsPlaquetteAt L t y p ∧ h p ≠ 0
variable {R : StepSetup} (A : ResponseSetup R)
def supportResponseSum (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    CaseFunction R n :=
  fun W Yt ωt _ b =>
    ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
        centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f +
      R.params.coupling / 2 * A.coeff * ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
        blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y
def centeredSupportResponse (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    CaseFunction R n :=
  fun W Yt ωt bad b => supportResponseSum A V f W Yt ωt bad b -
    caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)
end SupportMoments
end YangMills.Construction.ResponseInTheExpansion
end
