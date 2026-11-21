import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import YangMills.Construction.SixteenPointsOnASmallTorus.ResponseOfACopyIsBounded
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmallTorusCopies
open StepSettings TorusLumps TorusFields WeightedResponses ResponseInTheExpansion
private theorem abs_supportResponseTotal_le {R : StepSetup} {A : ResponseSetup R} (hA : A.IsAdmissible)
    (hC₀ : 1 ≤ A.responseParams.C₀) {n : ℕ} [NeZero n]
    (hs : IsBlockTorusSide R.params n) (f : PlaquetteWeight (fineSide R.params.side R.depth n))
    (hf : weightNorm R.params.side R.depth f ≤ 1) (W : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → R.labels.Ω) (hq : IsLiveState R.params R.coupling R.labelWeight W Y ω) :
    |supportResponseTotal A f W Y ω| ≤
      A.responseParams.C₀ * ((weightSupportSites R.params.side R.depth n f).card : ℝ) *
        meanSiteScore A.score (weightSupportSites R.params.side R.depth n f) Y ω := by apply _root_.YangMills.SharedProofs.p79992 <;> assumption
theorem responseBoundedByScore : responseBoundedByScoreStatement := by
  unfold responseBoundedByScoreStatement ForAllLargeFloors ForAllInitialStages
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ Kr => ⟨0, fun y _ => ?_⟩⟩
  intro β hL z₀ _ s hst n _ hb f hf W Y ω hq
  have hz := hst s le_rfl
  have hA := hz.onFamily.admissible
  have hK := hz.params_eq
  have hfit := hA.params_admissible
  have ha : (1 : ℝ) ≤ (T.stepParameters y).coupling := hT.a_ge
  have hC : 1 ≤ (flowStages T y β hL z₀ s).2.responseParams.C₀ := by
    rw [hfit.C₀_eq]
    have h₁ := hfit.N₀_nonneg
    have h₂ := hfit.Kc_ge
    have h₃ : (1 : ℝ) ≤ (flowStages T y β hL z₀ s).1.toStepSetup.params.coupling := ha
    nlinarith
  have h := abs_supportResponseTotal_le hA hC hb f hf W Y ω hq
  rw [hK] at h
  exact h
end YangMills.Construction.SmallTorusCopies
end
