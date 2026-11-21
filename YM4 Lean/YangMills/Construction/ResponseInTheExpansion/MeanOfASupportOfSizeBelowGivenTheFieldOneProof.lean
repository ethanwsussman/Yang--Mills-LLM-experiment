import YangMills.Construction.ResponseInTheExpansion.MeanOfASupportOfSizeBelowGivenTheFieldOne
import YangMills.Construction.TransfersOffTheWalk.MeanOfASupportGivenTheFieldOneProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings StepGas RenormalizationStepParameters TorusFields TorusLumps FreeEnergies WeightedResponses BlockAverages HoledShares ColdStepAtMirrorFrames
namespace SupportResponseMean
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Sizes
variable {A : ResponseSetup R}
private theorem blockBondScores_abs_le (hS : BondScoreProperties) (hfit : R.params.Admissible) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : StepCosts.BaseChoice R.params.side n) (Y : TorusSite n) : |blockBondScores (R := R) W V b Y| ≤ 16 := by apply _root_.YangMills.SharedProofs.p16371 <;> assumption
private theorem exists_lowerSite_parent (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) {Y : TorusSite n} (hY : Y ∈ upperSites f) :
    ∃ y ∈ lowerSites f, parentBlock R.params.side y = Y := by apply _root_.YangMills.SharedProofs.p21292 <;> assumption
private theorem card_upperSites_le (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    (upperSites (R := R) f).card ≤ (lowerSites f).card := by apply _root_.YangMills.SharedProofs.p7582 <;> assumption
omit [NeZero n] in
private theorem siteScore_nonneg (hs : ∀ w, 0 ≤ A.score w) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (y : TorusSite (n * R.params.side)) : 0 ≤ siteScore A.score Yt ωt y := by apply _root_.YangMills.SharedProofs.p27728 <;> assumption
private theorem params_bounds (hfit : R.params.Admissible) (hres : A.IsAdmissible) : 12 + 40 * R.params.coupling ≤ A.responseParams.C₀ ∧ 1 ≤ R.params.coupling := by apply _root_.YangMills.SharedProofs.p4770 <;> assumption
private theorem supportResponseSum_abs_le (hS : BondScoreProperties) (hW : WeightsCloseToBlockMeans) (hfit : R.params.Admissible)
    (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (h0 : weightNorm R.params.side R.depth f ≤ 1) {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω} (bad : Finset (TorusBond (n * R.params.side))) (b : StepCosts.BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    |supportResponseSum A V f W Yt ωt bad b| ≤
      (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Yt ωt := by
  classical
  obtain ⟨hC, ha⟩ := params_bounds hfit hres
  have hs := hres.price.nonneg
  have hodd := hfit.L_odd
  have hF : |∑ y ∈ lowerSites f, centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f| ≤
      A.responseParams.C₀ * ((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Yt ωt := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have each : ∀ y ∈ lowerSites f, |centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f| ≤ A.responseParams.C₀ + siteScore A.score Yt ωt y := by
      intro y _
      have h2 := hres.bounds.size_hull _ hb y W Yt ωt hl f
      have h3 : 0 ≤ A.responseParams.C₀ + siteScore A.score Yt ωt y := by
        have := siteScore_nonneg hs Yt ωt y
        linarith
      exact h2.trans (mul_le_of_le_one_right h3 h0)
    refine (Finset.sum_le_sum each).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rfl
  have hcoef : |R.params.coupling / 2 * A.coeff| ≤ R.params.coupling := by
    have hal := hres.abs_coeff_le
    rw [abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < R.params.coupling)]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    calc R.params.coupling / 2 * |A.coeff| ≤ R.params.coupling / 2 * 2 := mul_le_mul_of_nonneg_left hal (by linarith)
      _ = R.params.coupling := by ring
  have hsum : |∑ Y ∈ upperSites (R := R) f, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V b Y| ≤
      16 * ((lowerSites f).card : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have each : ∀ Y ∈ upperSites (R := R) f, |blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V b Y| ≤ 16 := by
      intro Y _
      have hh : |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1 :=
        ((hW R.params.side hodd (R.depth + 1) n Y).1 f).trans ((le_max_left _ _).trans h0)
      rw [abs_mul]
      calc _ ≤ 1 * 16 := mul_le_mul hh (blockBondScores_abs_le hS hfit W V b Y) (abs_nonneg _) zero_le_one
        _ = 16 := by norm_num
    refine (Finset.sum_le_sum each).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have : ((upperSites (R := R) f).card : ℝ) ≤ ((lowerSites f).card : ℝ) := by exact_mod_cast card_upperSites_le f
    linarith
  have hm : |R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites (R := R) f,
      blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V b Y| ≤ 16 * R.params.coupling * ((lowerSites f).card : ℝ) := by
    rw [abs_mul]
    calc _ ≤ R.params.coupling * (16 * ((lowerSites f).card : ℝ)) :=
          mul_le_mul hcoef hsum (abs_nonneg _) (by linarith)
      _ = _ := by ring
  show |∑ y ∈ lowerSites f, centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f +
    R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites (R := R) f, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V b Y| ≤ _
  refine (abs_add_le _ _).trans ?_
  linarith
abbrev _root_.YangMills.SharedProofs.p51635 := @supportResponseSum_abs_le
private theorem isLiveState_of_stepWeight_ne_zero (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params (n * R.params.side)) {C : Finset (TorusSite n)} {V : TorusField n}
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω} {bad : Finset (TorusBond (n * R.params.side))}
    {b : StepCosts.BaseChoice R.params.side n} (hh : IsHullState R.params R.range W Yt) (hw : stepWeight R C V W Yt ωt bad b ≠ 0) :
    IsLiveState R.params R.coupling R.labelWeight W Yt ωt := by apply _root_.YangMills.SharedProofs.p15857 <;> assumption
private theorem stepWeight_nonneg (hrow : R.HasExpansions) (hcut : IsCutoff R.ballRadius R.barrierFn) (hρ : 0 < R.ballRadius) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : StepCosts.BaseChoice R.params.side n) (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ωt bad b := by apply _root_.YangMills.SharedProofs.p32517 <;> assumption
private theorem abs_caseMean_le (hrow : R.HasExpansions) (hcut : IsCutoff R.ballRadius R.barrierFn) (hρ : 0 < R.ballRadius) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) {F B : CaseFunction R n} {c : ℝ}
    (hB : CaseIntegrable R C V q B)
    (hle : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → |F W Yt ωt bad b| ≤ c * B W Yt ωt bad b) :
    |caseMean R C V q F| ≤ c * caseMean R C V q B := by
  classical
  have hterm : ∀ bad Yt b W ν, ‖caseTerm R C V q F bad Yt b W ν‖ ≤ c * caseTerm R C V q B bad Yt b W ν := by
    intro bad Yt b W ν
    unfold caseTerm
    split_ifs with hcs
    · by_cases hw : stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = 0
      · simp [hw]
      · have h1 := hle _ _ _ bad b (isLiveState_of_stepWeight_ne_zero hrow hb hcs.1 hw)
        have h2 := stepWeight_nonneg hrow hcut hρ hb C V (q.fillLabels Yt ν) bad b hcs.1
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right h1 h2
    · simp
  have hI : |caseIntegral R C V q F| ≤ c * caseIntegral R C V q B := by
    unfold caseIntegral
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun bad hbad => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun Yt _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    have hi := hB bad hbad Yt b
    have hin : ∀ᵐ W ∂(fieldHaar (n * R.params.side)), Integrable (fun ν => caseTerm R C V q B bad Yt b W ν)
        (Measure.pi fun _ => R.labels.μ) := hi.prod_right_ae
    have hout : Integrable (fun W => ∫ ν, caseTerm R C V q B bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ))
        (fieldHaar (n * R.params.side)) := hi.integral_prod_left
    have hh : ‖∫ W, ∫ ν, caseTerm R C V q F bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))‖ ≤
        ∫ W, c * ∫ ν, caseTerm R C V q B bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
      refine norm_integral_le_of_norm_le (hout.const_mul c) (hin.mono fun W hW => ?_)
      have h2 : ‖∫ ν, caseTerm R C V q F bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ)‖ ≤
          ∫ ν, c * caseTerm R C V q B bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) :=
        norm_integral_le_of_norm_le (hW.const_mul c) (Filter.Eventually.of_forall fun ν => hterm bad Yt b W ν)
      rwa [integral_const_mul] at h2
    rw [integral_const_mul, Real.norm_eq_abs] at hh
    exact hh
  have hZ : 0 ≤ coarseStateWeight R C V q := ENNReal.toReal_nonneg
  unfold caseMean
  rw [abs_div, abs_of_nonneg hZ, mul_div_assoc']
  exact div_le_div_of_nonneg_right hI hZ
private theorem trivialField_isCold {σ : ℝ} (m : ℕ) (hσ : 0 < σ) : IsCold σ (trivialField m) := by apply _root_.YangMills.SharedProofs.p35782 <;> assumption
end Sizes
private theorem exp_le_one_add_two_mul {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : Real.exp u ≤ 1 + 2 * u := by apply _root_.YangMills.Construction.BlockAverages.SmoothWeightCurl.exp_le_one_add_two_mul <;> assumption
end SupportResponseMean
open SupportResponseMean in
theorem supportResponseMeanBound_holds (hM : meanSiteScoresStepBound) (hS : BondScoreProperties)
    (hW : WeightsCloseToBlockMeans) : supportResponseMeanBound := by
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
  refine ⟨max (max y₁ T.floorMin) (2 * (K.C₀ + 16 * T.coupling) / (7 * T.gasRate)), fun y hy R A hK hAt n _ hn f hs0 hne => ?_⟩
  have hy1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : 2 * (K.C₀ + 16 * T.coupling) / (7 * T.gasRate) ≤ y := (le_max_right _ _).trans hy
  have hR := hAt.onFamily
  have hfit : R.params.Admissible := hR.params_eq ▸ hT.fits y hy2
  have hrow : R.HasExpansions := hR.isStep.1
  have hres := hAt.admissible
  have hσ : 0 < R.params.threshold := hfit.σ_pos
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
  obtain ⟨hC, ha⟩ := params_bounds hfit hres
  have hs := hres.price.nonneg
  obtain ⟨Y₀, hY₀⟩ := hne
  obtain ⟨y₀', hy₀', -⟩ := exists_lowerSite_parent f hY₀
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
  have hparent : (∏ i : Fin 1, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks ((fun _ => lowerSites f) i))
      (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2) = 1 := by
    rw [Fin.prod_univ_one]
    unfold meanSiteScore
    have : ∀ z, siteScore (coarseLabelScore A.responseParams.s₁ A.score) (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2 z = 0 := by
      intro z
      unfold siteScore
      rw [dif_neg]
      exact Finset.notMem_empty _
    simp [this]
  rw [hparent, mul_one] at hMm
  have hEN : caseMean R ∅ (trivialField n) (emptyCoarseState R) (fun _ Yt ωt _ _ => meanSiteScore A.score (lowerSites f) Yt ωt) ≤ 1 + 2 * u := by
    refine le_trans (le_of_eq ?_) (hMm.trans hexp)
    show _ = caseMean R ∅ (trivialField n) (emptyCoarseState R) (prodMeanSiteScores A fun _ : Fin 1 => lowerSites f)
    congr 1
    funext _ Yt ωt _ _
    simp [prodMeanSiteScores]
  have hIN : CaseIntegrable R ∅ (trivialField n) (emptyCoarseState R) (fun _ Yt ωt _ _ => meanSiteScore A.score (lowerSites f) Yt ωt) := by
    have e : (fun (_ : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
        (_ : Finset (TorusBond (n * R.params.side))) (_ : StepCosts.BaseChoice R.params.side n) => meanSiteScore A.score (lowerSites f) Yt ωt) =
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
  have hS0 : ∀ (Y' : Finset (TorusSite (n * R.params.side))) (ω' : Y' → R.labels.Ω), 0 ≤ scoreSumOn A (lowerSites f) Y' ω' :=
    fun Y' ω' => Finset.sum_nonneg fun y _ => siteScore_nonneg hs Y' ω' y
  have hc0 : 0 ≤ c * ((lowerSites f).card : ℝ) := by positivity
  have hv : |caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| ≤
      c * ((lowerSites f).card : ℝ) * (1 + 2 * u) := by
    refine (abs_caseMean_le hrow hcut hρ hb ∅ (trivialField n) (emptyCoarseState R) hIN fun W' Y' ω' bad' b' hl' => ?_).trans
      (mul_le_mul_of_nonneg_left hEN hc0)
    refine (supportResponseSum_abs_le hS hW hfit hres hb (trivialField n) f hs0 bad' b' hl').trans ?_
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
end YangMills.Construction.ResponseInTheExpansion
end
