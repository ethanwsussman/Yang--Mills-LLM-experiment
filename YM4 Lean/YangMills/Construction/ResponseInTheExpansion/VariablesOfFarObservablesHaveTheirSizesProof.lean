import YangMills.Construction.ResponseInTheExpansion.MeanOfASupportOfSizeBelowGivenTheFieldOneProof
import YangMills.Construction.ResponseInTheExpansion.VariablesOfFarObservablesHaveTheirSizes
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings TorusFields TorusLumps StepCosts StepGas RenormalizationStepParameters FreeEnergies ColdStepAtMirrorFrames WeightedResponses
  TorusContours
namespace FarObservableBounds
variable {R : StepSetup} {n : ℕ} [NeZero n]
section GaugeInvariance
private theorem isHullState_gaugeTransform (hfit : R.params.Admissible)
    (g : TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion) (W : TorusField (n * R.params.side)) (r : ℕ)
    (Y : Finset (TorusSite (n * R.params.side))) :
    IsHullState R.params r (TorusFields.gaugeTransform g W) Y ↔ IsHullState R.params r W Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.isHullState_gaugeTransform_iff <;> assumption
private theorem isLiveState_gaugeTransform (hfit : R.params.Admissible) (hrow : R.HasExpansions)
    (hb : IsBlockTorusSide R.params (n * R.params.side))
    (u : TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion) {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    (h : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    IsLiveState R.params R.coupling R.labelWeight (TorusFields.gaugeTransform u W) Yt (R.labels.act Yt u ωt) := by
  refine ⟨(isHullState_gaugeTransform hfit u W _ Yt).mpr h.1, ?_⟩
  rw [hrow.2.gauge _ hb W Yt ωt u h.1]
  exact h.2
private theorem supportResponseSum_gaugeTransform (A : ResponseSetup R) (hres : A.IsAdmissible)
    (hb : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    (bad : Finset (TorusBond (n * R.params.side))) {b : BaseChoice R.params.side n}
    {u : TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion}
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt)
    (hu : ∀ e, u (toTorusSite (n * R.params.side) (b e)) = 1) :
    supportResponseSum A V f (TorusFields.gaugeTransform u W) Yt (R.labels.act Yt u ωt) bad b =
      supportResponseSum A V f W Yt ωt bad b := by apply _root_.YangMills.SharedProofs.p54822 <;> assumption
end GaugeInvariance
section Measurability
private theorem measurable_centeredSupportResponse (hS : BondScoreProperties) (hfit : R.params.Admissible)
    (hrow : R.HasExpansions) (A : ResponseSetup R)
    (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      liveCaseFunction (centeredSupportResponse A V f) p.1 Yt p.2 bad b := by apply _root_.YangMills.SharedProofs.p81506 <;> assumption
end Measurability
section Bounds
variable {A : ResponseSetup R}
private theorem exists_lowerSite_parentBlock_eq (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    {Y : TorusSite n} (hY : Y ∈ upperSites f) :
    ∃ y ∈ lowerSites f, parentBlock R.params.side y = Y := by apply _root_.YangMills.SharedProofs.p21292 <;> assumption
private theorem siteScore_nonneg (hs : ∀ w, 0 ≤ A.score w) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (y : TorusSite (n * R.params.side)) : 0 ≤ siteScore A.score Yt ωt y := by apply _root_.YangMills.SharedProofs.p46846 <;> assumption
private theorem C₀_ge_and_coupling_ge (hfit : R.params.Admissible) (hres : A.IsAdmissible) :
    12 + 40 * R.params.coupling ≤ A.responseParams.C₀ ∧ 1 ≤ R.params.coupling := by apply _root_.YangMills.SharedProofs.p4770 <;> assumption
private theorem abs_supportResponseSum_le (hS : BondScoreProperties) (hW : WeightsCloseToBlockMeans)
    (hfit : R.params.Admissible) (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (h0 : weightNorm R.params.side R.depth f ≤ 1) {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    |supportResponseSum A V f W Yt ωt bad b| ≤
      (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Yt ωt := by apply _root_.YangMills.SharedProofs.p51635 <;> assumption
private theorem abs_caseMean_le (hrow : R.HasExpansions) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hρ : 0 < R.ballRadius) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) {F B : CaseFunction R n} {c : ℝ} (hc : 0 ≤ c)
    (hB : CaseIntegrable R C V q B)
    (hle : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |F W Yt ωt bad b| ≤ c * B W Yt ωt bad b) :
    |caseMean R C V q F| ≤ c * caseMean R C V q B := by apply _root_.YangMills.SharedProofs.p20584 <;> assumption
private theorem trivialField_isCold {σ : ℝ} (m : ℕ) (hσ : 0 < σ) : IsCold σ (trivialField m) := by apply _root_.YangMills.SharedProofs.p35782 <;> assumption
end Bounds
end FarObservableBounds
open FarObservableBounds in
theorem centeredSupportResponseBounds_holds (hM : meanSiteScoresStepBound) (hS : BondScoreProperties)
    (hW : WeightsCloseToBlockMeans) : centeredSupportResponseBounds := by
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
  refine ⟨max (max y₁ T.floorMin) (1 / T.gasRate), fun y hy R A hK hAt n _ hn V f hs0 hne => ?_⟩
  have hy1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : 1 / T.gasRate ≤ y := (le_max_right _ _).trans hy
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
  refine ⟨fun Yt bad b => measurable_centeredSupportResponse hS hfit hrow A hres hb V f Yt bad b, ?_, ?_⟩
  · intro W Yt ωt bad b u hl hu _
    unfold liveCaseFunction
    rw [if_pos (isLiveState_gaugeTransform hfit hrow hb u hl), if_pos hl]
    unfold centeredSupportResponse
    rw [supportResponseSum_gaugeTransform A hres hb V f bad hl hu]
  · intro W Yt ωt bad b hl
    obtain ⟨hC, ha⟩ := C₀_ge_and_coupling_ge hfit hres
    have hs := hres.price.nonneg
    obtain ⟨Y₀, hY₀⟩ := hne
    obtain ⟨y₀', hy₀', -⟩ := exists_lowerSite_parentBlock_eq f hY₀
    have hcard : (0 : ℝ) < ((lowerSites f).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨y₀', hy₀'⟩
    obtain ⟨hMi, hMm⟩ := hM y hy1 R A hK hAt n (coldCaseGround R (trivialField n))
      (Or.inl ⟨hn, trivialField_isCold n (by positivity), rfl, rfl, rfl⟩) 1 (fun _ => lowerSites f)
      (fun _ => ⟨y₀', hy₀'⟩) (fun i j hij => absurd (Subsingleton.elim i j) hij)
    have hx1 : 1 ≤ T.gasRate * R.coupling := by
      have h1 : 1 / T.gasRate ≤ R.coupling := hy3.trans hR.le_coupling
      rw [div_le_iff₀ hch] at h1
      linarith
    have hexp : Real.exp (((1 : ℕ) : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling))) ≤ 3 / 2 := by
      have hu1 : Real.exp (-(7 * T.gasRate * R.coupling)) ≤ 1 / 8 := by
        have h1 := Real.add_one_le_exp (7 * T.gasRate * R.coupling)
        have h2 : Real.exp (-(7 * T.gasRate * R.coupling)) * Real.exp (7 * T.gasRate * R.coupling) = 1 := by
          rw [← Real.exp_add]
          simp
        have h3 := Real.exp_pos (-(7 * T.gasRate * R.coupling))
        nlinarith
      have hu0 := Real.exp_pos (-(7 * T.gasRate * R.coupling))
      obtain ⟨u, hu⟩ : ∃ u, u = Real.exp (-(7 * T.gasRate * R.coupling)) := ⟨_, rfl⟩
      rw [← hu] at hu1 hu0 ⊢
      rw [Nat.cast_one, one_mul]
      have h1 := Real.add_one_le_exp (-u)
      have h2 : Real.exp u * Real.exp (-u) = 1 := by
        rw [← Real.exp_add]
        simp
      by_contra hcon
      push Not at hcon
      have h3 : (7 : ℝ) / 8 ≤ Real.exp (-u) := by linarith
      nlinarith
    have hparent : (∏ i : Fin 1, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
        (parentBlocks ((fun _ => lowerSites f) i))
        (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2) = 1 := by
      rw [Fin.prod_univ_one]
      unfold meanSiteScore
      have : ∀ z, siteScore (coarseLabelScore A.responseParams.s₁ A.score) (coldCaseGround R (trivialField n)).state.1
          (coldCaseGround R (trivialField n)).state.2 z = 0 := by
        intro z
        unfold siteScore
        rw [dif_neg]
        exact Finset.notMem_empty _
      simp [this]
    rw [hparent, mul_one] at hMm
    have hEN : caseMean R ∅ (trivialField n) (emptyCoarseState R)
        (fun _ Yt ωt _ _ => meanSiteScore A.score (lowerSites f) Yt ωt) ≤ 3 / 2 := by
      refine le_trans (le_of_eq ?_) (hMm.trans hexp)
      show _ = caseMean R ∅ (trivialField n) (emptyCoarseState R) (prodMeanSiteScores A fun _ : Fin 1 => lowerSites f)
      congr 1
      funext _ Yt ωt _ _
      simp [prodMeanSiteScores]
    have hIN : CaseIntegrable R ∅ (trivialField n) (emptyCoarseState R)
        (fun _ Yt ωt _ _ => meanSiteScore A.score (lowerSites f) Yt ωt) := by
      have e : (fun (_ : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
          (ωt : Yt → R.labels.Ω) (_ : Finset (TorusBond (n * R.params.side))) (_ : BaseChoice R.params.side n) =>
          meanSiteScore A.score (lowerSites f) Yt ωt) =
          prodMeanSiteScores A fun _ : Fin 1 => lowerSites f := by
        funext _ Yt ωt _ _
        simp [prodMeanSiteScores]
      rw [e]
      exact hMi
    have hN : ∀ (Y' : Finset (TorusSite (n * R.params.side))) (ω' : Y' → R.labels.Ω),
        ((lowerSites f).card : ℝ) * meanSiteScore A.score (lowerSites f) Y' ω' =
          ((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Y' ω' := by
      intro Y' ω'
      unfold meanSiteScore scoreSumOn
      field_simp
    have hS0 : ∀ (Y' : Finset (TorusSite (n * R.params.side))) (ω' : Y' → R.labels.Ω),
        0 ≤ scoreSumOn A (lowerSites f) Y' ω' :=
      fun Y' ω' => Finset.sum_nonneg fun y _ => siteScore_nonneg hs Y' ω' y
    have hc1 : 1 ≤ A.responseParams.C₀ + 16 * R.params.coupling := by linarith
    have hc0 : 0 ≤ (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) := by positivity
    have hv : |caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| ≤
        (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) * (3 / 2) := by
      refine (abs_caseMean_le hrow hcut hρ hb ∅ (trivialField n) (emptyCoarseState R) hc0 hIN
        fun W' Y' ω' bad' b' hl' => ?_).trans (mul_le_mul_of_nonneg_left hEN hc0)
      refine (abs_supportResponseSum_le hS hW hfit hres hb (trivialField n) f hs0 bad' b' hl').trans ?_
      have h1 := hN Y' ω'
      have h2 := hS0 Y' ω'
      show _ ≤ (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) *
        meanSiteScore A.score (lowerSites f) Y' ω'
      rw [mul_assoc, h1]
      nlinarith
    have hF := abs_supportResponseSum_le hS hW hfit hres hb V f hs0 bad b hl
    unfold centeredSupportResponse
    refine (abs_sub _ _).trans ?_
    have h1 := hN Yt ωt
    have h2 := hS0 Yt ωt
    show _ ≤ 4 * (A.responseParams.C₀ * ((lowerSites f).card : ℝ)) * meanSiteScore A.score (lowerSites f) Yt ωt
    have e : 4 * (A.responseParams.C₀ * ((lowerSites f).card : ℝ)) * meanSiteScore A.score (lowerSites f) Yt ωt =
        4 * A.responseParams.C₀ * (((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Yt ωt) := by
      rw [← h1]
      ring
    rw [e]
    nlinarith
end YangMills.Construction.ResponseInTheExpansion
end
