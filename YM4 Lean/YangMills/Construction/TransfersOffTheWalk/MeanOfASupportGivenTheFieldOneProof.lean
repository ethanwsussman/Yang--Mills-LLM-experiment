import YangMills.Construction.ColdChainAtEveryLevel.SmoothWeightsThroughTheCurlProof
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportVariablesHaveTheirSizesProof
import YangMills.Construction.TransfersOffTheWalk.MeanOfASupportGivenTheFieldOne
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TransfersOffTheWalk
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepGas WeightedResponses FreeEnergies ResponseInTheExpansion
  ColdStepAtMirrorFrames
namespace SupportMeanAtTrivialField
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Sizes
variable {A : ResponseSetup R}
private theorem exists_lowerSite_of_mem_upperSites
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) {Y : TorusSite n}
    (hY : Y ∈ upperSites f) :
    ∃ y ∈ lowerSites f, parentBlock R.params.side y = Y := by apply _root_.YangMills.SharedProofs.p21292 <;> assumption
omit [NeZero n] in
private theorem siteScore_nonneg (hs : ∀ w, 0 ≤ A.score w) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (y : TorusSite (n * R.params.side)) : 0 ≤ siteScore A.score Yt ωt y := by
  classical
  unfold siteScore
  split_ifs
  · exact hs _
  · exact le_rfl
abbrev _root_.YangMills.SharedProofs.p27728 := @siteScore_nonneg
private theorem C₀_ge_and_one_le_coupling (hadm : R.params.Admissible) (hres : A.IsAdmissible) :
    12 + 40 * R.params.coupling ≤ A.responseParams.C₀ ∧ 1 ≤ R.params.coupling := by apply _root_.YangMills.SharedProofs.p4770 <;> assumption
private theorem abs_supportResponseSum_le (hS : BondScoreProperties) (hW : WeightsCloseToBlockMeans)
    (hadm : R.params.Admissible) (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (h1 : weightNorm R.params.side (R.depth + 1) f ≤ 1) (h0 : weightNorm R.params.side R.depth f ≤ 1)
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    (bad : Finset (TorusBond (n * R.params.side))) (b : StepCosts.BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    |supportResponseSum A V f W Yt ωt bad b| ≤
      (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) +
        scoreSumOn A (lowerSites f) Yt ωt := by apply _root_.YangMills.SharedProofs.p46704 <;> assumption
private theorem abs_caseMean_le (hrow : R.HasExpansions) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hρ : 0 < R.ballRadius) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) {F B : CaseFunction R n} {c : ℝ}
    (hc : 0 ≤ c) (hB : CaseIntegrable R C V q B)
    (hle : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |F W Yt ωt bad b| ≤ c * B W Yt ωt bad b) :
    |caseMean R C V q F| ≤ c * caseMean R C V q B := by apply _root_.YangMills.SharedProofs.p20584 <;> assumption
private theorem trivialField_isCold {σ : ℝ} (m : ℕ) (hσ : 0 < σ) : IsCold σ (trivialField m) := by apply _root_.YangMills.SharedProofs.p35782 <;> assumption
end Sizes
private theorem exp_le_one_add_two_mul {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : Real.exp u ≤ 1 + 2 * u := by apply _root_.YangMills.Construction.BlockAverages.SmoothWeightCurl.exp_le_one_add_two_mul <;> assumption
end SupportMeanAtTrivialField
open SupportMeanAtTrivialField in
theorem supportResponseMeanAtTrivialFieldBound_holds (hM : meanSiteScoresStepBound) (hS : BondScoreProperties)
    (hW : WeightsCloseToBlockMeans) : supportResponseMeanAtTrivialFieldBound := by
  classical
  obtain ⟨rt₀, hrt₀, hM⟩ := hM
  refine ⟨rt₀, hrt₀, fun T hT hrt K => ?_⟩
  obtain ⟨y₁, hM⟩ := hM T hT hrt K
  have hκ₁ : 0 < T.κ₁ := by
    have h1 := hT.κ_pos
    have h2 := hT.cE_pos
    have h3 := hT.σ_pos
    unfold ParameterAssignment.κ₁
    exact lt_min (by positivity) (by positivity)
  have hch : 0 < T.gasRate := by
    have h1 := hT.κ_pos
    have h2 := hT.cE_pos
    have h3 := hT.σ_pos
    unfold ParameterAssignment.gasRate
    exact mul_pos (by positivity) (lt_min h2 (lt_min (by positivity) (by positivity)))
  refine ⟨max (max y₁ T.floorMin) (2 * (K.C₀ + 16 * T.coupling) / (7 * T.gasRate)),
    fun y hy R A hK hAt n _ hn f hs1 hs0 hne => ?_⟩
  have hy1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : 2 * (K.C₀ + 16 * T.coupling) / (7 * T.gasRate) ≤ y := (le_max_right _ _).trans hy
  have hR := hAt.onFamily
  have hadm : R.params.Admissible := hR.params_eq ▸ hT.fits y hy2
  have hrow : R.HasExpansions := hR.isStep.1
  have hres := hAt.admissible
  have hσ : 0 < R.params.threshold := hadm.σ_pos
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    positivity
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [hR.params_eq]
      rfl
    rw [e, hR.barrierFn_eq]
    exact hT.cut
  have hb : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left n rfl, ?_⟩
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ hn
  obtain ⟨hC, ha⟩ := C₀_ge_and_one_le_coupling hadm hres
  have hs := hres.price.nonneg
  obtain ⟨Y₀, hY₀⟩ := hne
  obtain ⟨y₀', hy₀', -⟩ := exists_lowerSite_of_mem_upperSites f hY₀
  obtain ⟨hMi, hMm⟩ := hM y hy1 R A hK hAt n (coldCaseGround R (trivialField n))
    (Or.inl ⟨hn, trivialField_isCold n (by positivity), rfl, rfl, rfl⟩) 1 (fun _ => lowerSites f)
    (fun _ => ⟨y₀', hy₀'⟩) (fun i j hij => absurd (Subsingleton.elim i j) hij)
  obtain ⟨c, hcd⟩ : ∃ c, c = A.responseParams.C₀ + 16 * R.params.coupling := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by
    rw [hcd]
    linarith
  obtain ⟨u, hu⟩ : ∃ u, u = Real.exp (-(7 * T.gasRate * R.coupling)) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by
    rw [hu]
    exact (Real.exp_pos _).le
  have huc : 2 * c * u ≤ 1 := by
    have hRa : R.params.coupling = T.coupling := by
      rw [hR.params_eq]
      rfl
    have h7 : 0 < 7 * T.gasRate := by positivity
    have h1 : 2 * c ≤ 7 * T.gasRate * R.coupling := by
      have h2 := (div_le_iff₀ h7).mp (hy3.trans hR.le_coupling)
      rw [hcd, hK, hRa]
      linarith
    have h3 := Real.add_one_le_exp (7 * T.gasRate * R.coupling)
    have h4 : Real.exp (7 * T.gasRate * R.coupling) * u = 1 := by
      rw [hu, ← Real.exp_add]
      simp
    have h5 : 2 * c ≤ Real.exp (7 * T.gasRate * R.coupling) := by linarith
    calc 2 * c * u ≤ Real.exp (7 * T.gasRate * R.coupling) * u := mul_le_mul_of_nonneg_right h5 hu0
      _ = 1 := h4
  have hu2 : u ≤ 1 / 2 := by nlinarith
  have hexp : Real.exp (((1 : ℕ) : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling))) ≤ 1 + 2 * u := by
    rw [← hu, Nat.cast_one, one_mul]
    exact exp_le_one_add_two_mul hu0 hu2
  have hparent : (∏ i : Fin 1, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
      (parentBlocks ((fun _ => lowerSites f) i))
      (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2) = 1 := by
    rw [Fin.prod_univ_one]
    unfold meanSiteScore
    have : ∀ z, siteScore (coarseLabelScore A.responseParams.s₁ A.score)
        (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2 z = 0 := by
      intro z
      unfold siteScore
      rw [dif_neg]
      exact Finset.notMem_empty _
    simp [this]
  rw [hparent, mul_one] at hMm
  have hEN : caseMean R ∅ (trivialField n) (emptyCoarseState R)
      (fun _ Yt ωt _ _ => meanSiteScore A.score (lowerSites f) Yt ωt) ≤ 1 + 2 * u := by
    refine le_trans (le_of_eq ?_) (hMm.trans hexp)
    show _ = caseMean R ∅ (trivialField n) (emptyCoarseState R)
      (prodMeanSiteScores A fun _ : Fin 1 => lowerSites f)
    congr 1
    funext _ Yt ωt _ _
    simp [prodMeanSiteScores]
  have hIN : CaseIntegrable R ∅ (trivialField n) (emptyCoarseState R)
      (fun _ Yt ωt _ _ => meanSiteScore A.score (lowerSites f) Yt ωt) := by
    have e : (fun (_ : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
        (ωt : Yt → R.labels.Ω) (_ : Finset (TorusBond (n * R.params.side))) (_ : StepCosts.BaseChoice R.params.side n) =>
          meanSiteScore A.score (lowerSites f) Yt ωt) =
        prodMeanSiteScores A fun _ : Fin 1 => lowerSites f := by
      funext _ Yt ωt _ _
      simp [prodMeanSiteScores]
    rw [e]
    exact hMi
  have hcard : (0 : ℝ) < ((lowerSites f).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨y₀', hy₀'⟩
  have hN : ∀ (Y' : Finset (TorusSite (n * R.params.side))) (ω' : Y' → R.labels.Ω),
      ((lowerSites f).card : ℝ) * meanSiteScore A.score (lowerSites f) Y' ω' =
        ((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Y' ω' := by
    intro Y' ω'
    unfold meanSiteScore scoreSumOn
    field_simp
  have hS0 : ∀ (Y' : Finset (TorusSite (n * R.params.side))) (ω' : Y' → R.labels.Ω),
      0 ≤ scoreSumOn A (lowerSites f) Y' ω' :=
    fun Y' ω' => Finset.sum_nonneg fun y _ => siteScore_nonneg hs Y' ω' y
  have hc0 : 0 ≤ c * ((lowerSites f).card : ℝ) := by positivity
  have hv : |caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| ≤
      c * ((lowerSites f).card : ℝ) * (1 + 2 * u) := by
    refine (abs_caseMean_le hrow hcut hρ hb ∅ (trivialField n) (emptyCoarseState R) hc0 hIN
      fun W' Y' ω' bad' b' hl' => ?_).trans (mul_le_mul_of_nonneg_left hEN hc0)
    refine (abs_supportResponseSum_le hS hW hadm hres hb (trivialField n) f hs1 hs0 bad' b' hl').trans ?_
    have h1 := hN Y' ω'
    have h2 := hS0 Y' ω'
    show _ ≤ c * ((lowerSites f).card : ℝ) * meanSiteScore A.score (lowerSites f) Y' ω'
    rw [mul_assoc, h1, ← hcd]
    nlinarith
  refine hv.trans ?_
  have e : (A.responseParams.C₀ + 1 + 16 * R.params.coupling) = c + 1 := by
    rw [hcd]
    ring
  rw [e]
  have hfin : c * (1 + 2 * u) ≤ c + 1 := by nlinarith
  calc c * ((lowerSites f).card : ℝ) * (1 + 2 * u) = c * (1 + 2 * u) * ((lowerSites f).card : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfin hcard.le
end YangMills.Construction.TransfersOffTheWalk
end
