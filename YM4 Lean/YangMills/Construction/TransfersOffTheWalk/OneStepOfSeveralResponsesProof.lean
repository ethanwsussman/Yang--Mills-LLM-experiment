import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.EvaluationsOfAStateAreBorel
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import YangMills.Construction.ClusterExpansionOfAStep.ShiftsOfTwoSettings
import YangMills.Construction.FreeEnergiesOfTheFlow.LabelsOfAConfiguration
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanScoresOverTheGas
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportVariableInASetting
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportVariablesHaveTheirSizes
import YangMills.Construction.ResponseInTheExpansion.CaseMeanIsAMeanOfTheGas
import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitInASetting
import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitOverTheGas
import YangMills.Construction.TransfersOffTheWalk.MeanOfASupportGivenTheFieldOne
import YangMills.Construction.TransfersOffTheWalk.OneStepOfSeveralResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory
namespace TransfersOffTheWalk
open Dobrushin StepSettings StepGas RenormalizationStepParameters TorusFields TorusLumps WeightedResponses ResponseInTheExpansion FreeEnergies
open StateMeasurability SettingShifts ColdStepAtMirrorFrames BlockAverages StepCosts
namespace SeveralResponses
section Cases
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem caseTerm_liveCaseFunction
    (hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      IsHullState R.params R.range W Yt → 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) (F : CaseFunction R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V q (liveCaseFunction F) bad Yt b W ν = caseTerm R C V q F bad Yt b W ν := by
  classical
  unfold caseTerm
  split_ifs with h
  · unfold liveCaseFunction
    split_ifs with hl
    · rfl
    · have hz : R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) = 0 := by
        by_contra hne
        exact hl ⟨h.1, lt_of_le_of_ne (hnn _ _ _ h.1) (Ne.symm hne)⟩
      simp [stepWeight, hz]
  · rfl
abbrev _root_.YangMills.SharedProofs.p99396 := @caseTerm_liveCaseFunction
private theorem caseMean_liveCaseFunction
    (hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      IsHullState R.params R.range W Yt → 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) (F : CaseFunction R n) :
    caseMean R C V q (liveCaseFunction F) = caseMean R C V q F := by
  unfold caseMean caseIntegral
  simp only [caseTerm_liveCaseFunction hnn]
private theorem caseIntegrable_liveCaseFunction
    (hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      IsHullState R.params R.range W Yt → 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt)
    {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n} {F : CaseFunction R n}
    (h : CaseIntegrable R C V q F) : CaseIntegrable R C V q (liveCaseFunction F) := by
  intro bad hbad Yt b
  simp only [caseTerm_liveCaseFunction hnn]
  exact h bad hbad Yt b
omit [NeZero n] in
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν := by
  classical
  refine measurable_pi_lambda _ fun z => ?_
  rcases hl : q.labelAt z.1 with u | a
  · have hr : z.1 ∈ q.unlabelled Yt := Finset.mem_filter.mpr ⟨z.2, hl⟩
    have e : (fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν z) = fun ν => ν ⟨z.1, hr⟩ := by
      funext ν
      unfold CoarseState.fillLabels
      split
      · rename_i a' h
        rw [hl] at h
        cases h
      · rfl
    rw [e]
    exact measurable_pi_apply _
  · have e : (fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν z) = fun _ => a := by
      funext ν
      unfold CoarseState.fillLabels
      split
      · rename_i a' h
        rw [hl] at h
        cases h
        rfl
      · rename_i u h
        rw [hl] at h
        cases h
    rw [e]
    exact measurable_const
abbrev _root_.YangMills.SharedProofs.p55409 := @measurable_fillLabels
private theorem caseIntegrable_of_abs_le
    (hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      IsHullState R.params R.range W Yt → 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt)
    {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n} {F H : CaseFunction R n} {c : ℝ} (hc : 0 ≤ c)
    (hH : CaseIntegrable R C V q H)
    (hpos : ∀ W Yt ωt bad b, 0 < H W Yt ωt bad b)
    (hHm : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => H p.1 Yt p.2 bad b)
    (hFm : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => liveCaseFunction F p.1 Yt p.2 bad b)
    (hle : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) →
      |F W Yt ωt bad b| ≤ c * H W Yt ωt bad b) :
    CaseIntegrable R C V q F := by
  classical
  intro bad hbad Yt b
  set μ := (fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ) with hμ
  have hΦ : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) :=
    (((measurable_fieldWithStoredLinks q.1).comp (measurable_const.prodMk measurable_id)).comp measurable_fst).prodMk
      ((measurable_fillLabels q Yt).comp measurable_snd)
  set g : TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ :=
    fun p => liveCaseFunction F p.1 Yt p.2 bad b / H p.1 Yt p.2 bad b with hg
  have hgm : Measurable g := (hFm Yt bad b).div (hHm Yt bad b)
  have heq : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) => caseTerm R C V q F bad Yt b p.1 p.2) =
      fun p => caseTerm R C V q H bad Yt b p.1 p.2 * g (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) := by
    funext p
    rw [← caseTerm_liveCaseFunction hnn]
    unfold caseTerm
    split_ifs with h
    · have := (hpos (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b).ne'
      simp only [hg]
      field_simp
    · simp
  have hmeas : AEStronglyMeasurable (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q F bad Yt b p.1 p.2) μ := by
    rw [heq]
    exact (hH bad hbad Yt b).aestronglyMeasurable.mul (hgm.comp hΦ).aestronglyMeasurable
  refine ((hH bad hbad Yt b).norm.const_mul c).mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  unfold caseTerm
  split_ifs with h
  · by_cases hw : stepWeight R C V (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b = 0
    · simp [hw]
    · have hD : R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) ≠ 0 :=
        fun e => hw (by simp [stepWeight, e])
      have hb : baseLaw (R := R) (q.fieldWithStoredLinks p.1) b ≠ 0 := fun e => hw (by simp [stepWeight, e])
      have hlive : IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) :=
        ⟨h.1, lt_of_le_of_ne (hnn _ _ _ h.1) (Ne.symm hD)⟩
      have hbases : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks p.1)) := by
        by_contra hn
        exact hb (by unfold baseLaw; rw [if_neg hn])
      have := hle _ _ _ bad b hlive hbases
      have hp := (hpos (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b)
      rw [abs_mul, Real.norm_eq_abs, abs_mul, abs_of_pos hp]
      calc _ ≤ c * H (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b *
            |stepWeight R C V (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b| := by gcongr
        _ = _ := by ring
  · simp
end Cases
section Sites
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem lowerSites_nonempty {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    (h : (upperSites f).Nonempty) : (lowerSites f).Nonempty := by
  classical
  rw [← parentBlocks_lowerSites] at h
  exact (Finset.image_nonempty.mp h)
private theorem lowerSites_disjoint {ι : Type} {I : Finset ι} {f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    {D : ℕ} (h : WellSeparated I f D) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (lowerSites (f i)) (lowerSites (f j)) := by
  classical
  intro i hi j hj hij
  refine Finset.disjoint_left.mpr fun y hy hy' => ?_
  have e₁ : parentBlock R.params.side y ∈ upperSites (f i) := by
    rw [← parentBlocks_lowerSites]
    exact Finset.mem_image_of_mem _ hy
  have e₂ : parentBlock R.params.side y ∈ upperSites (f j) := by
    rw [← parentBlocks_lowerSites]
    exact Finset.mem_image_of_mem _ hy'
  have := h.separated i hi j hj hij (parentBlock R.params.side y)
    ((mem_thickening _ _ _).mpr ⟨_, e₁, by rw [supDist_self]; omega⟩)
    (parentBlock R.params.side y) ((mem_thickening _ _ _).mpr ⟨_, e₂, by rw [supDist_self]; omega⟩)
  rw [supDist_self] at this
  have := h.eight_lt
  omega
private theorem measurable_siteScore {Ω : Type} [MeasurableSpace Ω] {s : Ω → ℝ} (hs : Measurable s) {m : ℕ}
    (Y : Finset (TorusSite m)) (y : TorusSite m) : Measurable fun ω : Y → Ω => siteScore s Y ω y := by
  classical
  unfold siteScore
  by_cases hy : y ∈ Y
  · simp only [hy, dite_true]
    exact hs.comp (measurable_pi_apply _)
  · simp only [hy, dite_false]
    exact measurable_const
abbrev _root_.YangMills.SharedProofs.p56706 := @measurable_siteScore
private theorem measurable_meanSiteScore {Ω : Type} [MeasurableSpace Ω] {s : Ω → ℝ} (hs : Measurable s) {m : ℕ} [NeZero m]
    (B Y : Finset (TorusSite m)) : Measurable fun ω : Y → Ω => meanSiteScore s B Y ω := by
  unfold meanSiteScore
  exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun y _ => measurable_siteScore hs Y y))
private theorem one_le_meanSiteScore {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {m : ℕ} [NeZero m]
    (B Y : Finset (TorusSite m)) (ω : Y → Ω) : 1 ≤ meanSiteScore s B Y ω := by
  unfold meanSiteScore
  have : 0 ≤ ∑ y ∈ B, siteScore s Y ω y := Finset.sum_nonneg fun y _ => siteScore_nonneg hs Y ω y
  have h2 : 0 ≤ ((B.card : ℝ))⁻¹ := by positivity
  nlinarith [mul_nonneg h2 this]
abbrev _root_.YangMills.SharedProofs.p45452 := @one_le_meanSiteScore
private theorem chartDensity_eq_zero_of_not_lt (s : ChartSetting R n) {η : FreeCoords s.free}
    (h : ¬ ∀ b, ‖η b‖ < R.ballRadius) : chartDensity s η = 0 := by
  unfold chartDensity ChartSetting.cutoffProduct
  simp only [coordNorm_eq_norm]
  have hz : ∏ b : s.free, cutoffFactor R.ballRadius R.barrierFn ‖η b‖ = 0 := by
    simp only [not_forall, not_lt] at h
    obtain ⟨b, hb⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
    unfold cutoffFactor
    rw [if_neg (not_lt.mpr hb)]
  rw [hz]
  simp
private theorem weightedMean_congr_inBalls (s : ChartSetting R n) {F F' : FreeCoords s.free → ℝ}
    (h : ∀ η, s.InBalls η → F η = F' η) :
    weightedMean (chartDensity s) F = weightedMean (chartDensity s) F' := by
  unfold weightedMean
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  by_cases hb : ∀ b, ‖η b‖ < R.ballRadius
  · have : s.InBalls η := fun b => by
      rw [coordNorm_eq_norm]
      exact (hb b).le
    simp only [h η this]
  · simp only [chartDensity_eq_zero_of_not_lt s hb, mul_zero]
abbrev _root_.YangMills.SharedProofs.p21928 := @weightedMean_congr_inBalls
end Sites
private theorem two_term_bound {Ca Cb p S K N' d₁ d₂ d e : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hp : 0 ≤ p) (hS : 1 ≤ S)
    (hK : 0 ≤ K) (hN : 0 ≤ N') (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (h₁ : d₁ ≤ d) (h₂ : d₂ ≤ d) (he : e ≤ Real.exp p) :
    Ca * p * S * d₁ * K * (e * N') + Cb * p ^ 2 * Real.exp (2 * p) * d₂ * K * N' ≤
      (Ca * p * Real.exp p + Cb * p ^ 2 * Real.exp (2 * p)) * S ^ 2 * d * (K * N') := by
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have h1S : 1 ≤ S ^ 2 := by nlinarith
  have hA : Ca * p * S * d₁ * K * (e * N') ≤ Ca * p * Real.exp p * S ^ 2 * d * (K * N') := by
    have e1 : Ca * p * S * d₁ * K * (e * N') = Ca * p * (e * S * d₁) * (K * N') := by ring
    have e2 : Ca * p * Real.exp p * S ^ 2 * d * (K * N') = Ca * p * (Real.exp p * S ^ 2 * d) * (K * N') := by ring
    rw [e1, e2]
    gcongr
  have hB : Cb * p ^ 2 * Real.exp (2 * p) * d₂ * K * N' ≤ Cb * p ^ 2 * Real.exp (2 * p) * S ^ 2 * d * (K * N') := by
    have e1 : Cb * p ^ 2 * Real.exp (2 * p) * d₂ * K * N' = Cb * p ^ 2 * Real.exp (2 * p) * (1 * d₂) * (K * N') := by ring
    have e2 : Cb * p ^ 2 * Real.exp (2 * p) * S ^ 2 * d * (K * N') =
        Cb * p ^ 2 * Real.exp (2 * p) * (S ^ 2 * d) * (K * N') := by ring
    rw [e1, e2]
    gcongr
  calc _ ≤ Ca * p * Real.exp p * S ^ 2 * d * (K * N') + Cb * p ^ 2 * Real.exp (2 * p) * S ^ 2 * d * (K * N') :=
        add_le_add hA hB
    _ = _ := by ring
private theorem integrable_and_abs_integral_sub_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {P Mp N : Ω → ℝ} {c : ℝ}
    (hP : AEStronglyMeasurable P μ) (hM : Integrable Mp μ) (hN : Integrable N μ)
    (hae : ∀ᵐ σ ∂μ, |P σ - Mp σ| ≤ c * N σ) :
    Integrable P μ ∧ |∫ σ, P σ ∂μ - ∫ σ, Mp σ ∂μ| ≤ c * ∫ σ, N σ ∂μ := by
  have hPint : Integrable P μ := by
    refine (hM.abs.add (hN.const_mul c)).mono' hP ?_
    filter_upwards [hae] with σ hσ
    rw [Real.norm_eq_abs]
    have h₁ : |P σ| ≤ |P σ - Mp σ| + |Mp σ| := by
      calc |P σ| = |(P σ - Mp σ) + Mp σ| := by rw [sub_add_cancel]
        _ ≤ _ := abs_add_le _ _
    simp only [Pi.add_apply]
    linarith
  refine ⟨hPint, ?_⟩
  rw [← integral_sub hPint hM, ← integral_const_mul]
  exact (abs_integral_le_integral_abs).trans (integral_mono_ae (hPint.sub hM).abs (hN.const_mul c) hae)
abbrev _root_.YangMills.SharedProofs.p39813 := @integrable_and_abs_integral_sub_le
private theorem weightLipschitz_le_succ {L : ℕ} (t : ℕ) {m : ℕ} [NeZero m] (hL : 1 ≤ L) (h : PlaquetteWeight m) :
    weightLipschitz L t h ≤ weightLipschitz L (t + 1) h := by
  unfold weightLipschitz
  refine ciSup_mono (Set.finite_range _).bddAbove fun pp => ?_
  unfold barycentreDist
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  by_cases h0 : (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ) = 0
  · simp [h0]
  · have hd : 0 < (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)
    have hp : (0 : ℝ) < (L : ℝ) ^ t := by positivity
    have e1 : (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ) / (2 * (L : ℝ) ^ (t + 1)) ≤
        (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ) / (2 * (L : ℝ) ^ t) := by
      apply div_le_div_of_nonneg_left hd.le (by positivity)
      rw [pow_succ]
      nlinarith
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) e1
private theorem weightNorm_le_succ {L : ℕ} (t : ℕ) {m : ℕ} [NeZero m] (hL : 1 ≤ L) (h : PlaquetteWeight m) :
    weightNorm L t h ≤ weightNorm L (t + 1) h :=
  max_le_max le_rfl (weightLipschitz_le_succ t hL h)
end SeveralResponses
open SeveralResponses in
set_option maxHeartbeats 1600000 in
theorem severalResponsesStepDecorrelation_holds (hCase : WeightedResponses.caseMeanEqGasMeanStatement)
    (hScores : FreeEnergies.gasMeanScoreProductBound)
    (hSizes : FreeEnergies.supportResponseBoundStatement) (hVar : FreeEnergies.supportResponseLocalityStatement)
    (hMean : supportResponseMeanAtTrivialFieldBound) (hA : ResponseInTheExpansion.farSupportsDecorrelateInSetting)
    (hB : ResponseInTheExpansion.GasSupportMeansDecorrelate) (hWeight : ClusterExpansionOfAStep.GasIsActivityBounded)
    (hLaws : Dobrushin.ActivityConditionalLawsStatement)
    (hCfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) : WeightedObservables.severalResponsesStepDecorrelation := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hCase
  obtain ⟨r₂, p₂, H₂⟩ := hScores
  obtain ⟨r₃, p₃, H₃⟩ := hSizes
  obtain ⟨r₄, p₄, H₄⟩ := hVar
  obtain ⟨r₅, p₅, H₅⟩ := hA
  obtain ⟨r₆, p₆, H₆⟩ := hB
  obtain ⟨r₇, p₇, H₇⟩ := hWeight
  obtain ⟨r₉, p₉, H₉⟩ := hMean
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (min (r₅ c) (min (r₆ c) (min (r₇ c) (r₉ c))))))),
    fun c => ?_, ?_⟩
  · simp only [lt_min_iff]
    exact ⟨p₁ c, p₂ c, p₃ c, p₄ c, p₅ c, p₆ c, p₇ c, p₉ c⟩
  intro T hT hle K
  simp only [le_min_iff] at hle
  obtain ⟨l₁, l₂, l₃, l₄, l₅, l₆, l₇, l₉⟩ := hle
  obtain ⟨y₁, h₁⟩ := H₁ T hT l₁
  obtain ⟨y₂, h₂⟩ := H₂ T hT l₂ K
  obtain ⟨y₃, h₃⟩ := H₃ T hT l₃ K
  obtain ⟨y₄, h₄⟩ := H₄ T hT l₄ K
  obtain ⟨y₅, Ca, hCa, h₅⟩ := H₅ T hT l₅ K
  obtain ⟨y₆, Cb, hCb, h₆⟩ := H₆ T hT l₆ K
  obtain ⟨y₇, h₇⟩ := H₇ T hT l₇
  obtain ⟨y₈, h₈⟩ := hCfg T hT
  obtain ⟨y₉, h₉⟩ := H₉ T hT l₉ K
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (max y₈ (max y₉ (200 * T.B))))))))), fun p =>
    ⟨Ca * (p : ℝ) * Real.exp p + Cb * (p : ℝ) ^ 2 * Real.exp (2 * p),
      fun y hy R A₀ hK₀ htab₀ ι I A s hAK hAs htab n _ G hG f D hcard hsize hlive hr h8 hap => ?_⟩⟩
  simp only [max_le_iff] at hy
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₀⟩ := hy
  have hon := htab₀.onFamily
  have hrow : R.HasExpansions := hon.isStep.1
  have hLpos : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hside : R.params.n₀ ≤ n ∧ IsBlockTorusSide R.params (n * R.params.side) := by
    rcases hG with hc | hh
    · exact ⟨hc.n₀_le, Dvd.intro_left n rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hc.n₀_le⟩
    · have h₂ := hh.isBlockSide.2
      have h₃ : R.params.n₀ ≤ R.params.side * R.params.n₀ := Nat.le_mul_of_pos_left _ (by omega)
      exact ⟨h₃.trans h₂, Dvd.intro_left n rfl, h₂.trans (Nat.le_mul_of_pos_right _ (by omega))⟩
  have hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      IsHullState R.params R.range W Yt → 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt :=
    fun W Yt ωt h => hrow.2.nonneg _ hside.2 W Yt ωt h
  have hB₁ : 1 ≤ T.B := hT.B_ge
  have hxy : y ≤ R.coupling := hon.le_coupling
  have hX' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have := (abs_le.mp htab₀.abs_sub_le).2
    linarith
  have hxpos : 0 < R.coupling := by linarith
  have hP₁ := h₁ y e₁ R hon hX' n G hG
  have hW := h₇ y e₇ R hon hX' n G hG (fun j => j.1.Touches ∅)
  have hL := hLaws G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasureOff fun j => j.1.Touches ∅) G.weight _ hW
  have : IsProbabilityMeasure (G.gibbsLaw ∅) := hL.1
  by_cases hI : I.Nonempty
  swap
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hI
    have hone : CaseIntegrable R G.cut G.coarse G.state (fun _ _ _ _ _ => (1 : ℝ)) := by
      have := (h₂ y e₂ R A₀ hK₀ htab₀ n G hG ι ∅ (fun _ => ∅) (fun i hi => absurd hi (Finset.notMem_empty i))
        (fun i hi => absurd hi (Finset.notMem_empty i))).1
      simpa using this
    have hm := (hP₁.2 (fun _ _ _ _ _ => (1 : ℝ)) (fun _ _ _ => measurable_const)
      (fun _ _ _ _ _ _ _ _ _ => rfl) hone).2
    have hmean : caseMean R G.cut G.coarse G.state (fun _ _ _ _ _ => (1 : ℝ)) = 1 := by
      rw [hm]
      unfold gasExpectationOfCase GasGround.expectation
      have : ∀ᵐ σ ∂(G.gibbsLaw ∅), weightedMean (chartDensity (configSetting G σ)) (fun _ => (1 : ℝ)) = 1 := by
        filter_upwards [hP₁.1] with σ hσ
        unfold weightedMean
        simp only [one_mul]
        exact div_self hσ.2.ne'
      rw [integral_congr_ae this]
      simp
    refine ⟨by simpa using hone, fun i hi => absurd hi (Finset.notMem_empty i), ?_⟩
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [hmean]
    simp
  obtain ⟨i₀, hi₀⟩ := id hI
  obtain rfl : s = (A i₀).score := (hAs i₀ hi₀).symm
  have htab' := htab i₀ hi₀
  have hK' := hAK i₀ hi₀
  have hs := htab'.admissible.price
  have hP₂ := h₂ y e₂ R (A i₀) hK' htab'
  have ha1 : 1 ≤ R.params.coupling := by
    rw [hon.params_eq]
    exact hT.a_ge
  have hC₀' : 0 ≤ (A i₀).responseParams.C₀ := by
    have := htab'.admissible.params_admissible
    have h1 := this.C₀_eq
    have h2 := this.N₀_nonneg
    have h3 := this.Kc_ge
    rw [h1]
    linarith
  have hC₀ : 0 ≤ K.C₀ := by
    rwa [hK'] at hC₀'
  have hz : ∀ i ∈ I, weightNorm R.params.side R.depth (f i) ≤ 1 :=
    fun i hi => (weightNorm_le_succ R.depth hLpos (f i)).trans (hsize i hi)
  have hap' : WellSeparated I f D := ⟨hsize, hz, hlive, hr, h8, hap⟩
  set X : ι → CaseFunction R n := fun i => centeredSupportResponse (A i) G.coarse (f i) with hXdef
  set Fl : CaseFunction R n := fun W Yt ωt bad b => ∏ i ∈ I, liveCaseFunction (X i) W Yt ωt bad b with hFldef
  set Pr : CaseFunction R n := fun W Yt ωt bad b => ∏ i ∈ I, X i W Yt ωt bad b with hPrdef
  have hsz := fun i (hi : i ∈ I) => h₃ y e₃ R (A i) (hAK i hi) (htab i hi) n hside.1 G.coarse (f i) (hap'.norm_le i hi)
    (hap'.lower_norm_le i hi) (hap'.nonempty i hi)
  have hszb : ∀ i ∈ I, ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |X i W Yt ωt bad b| ≤ 4 * (K.C₀ * ((lowerSites (f i)).card : ℝ)) * meanSiteScore (A i₀).score (lowerSites (f i)) Yt ωt := by
    intro i hi W Yt ωt bad b hl
    have := (hsz i hi).2.2 W Yt ωt bad b hl
    unfold lowerSizeConst at this
    rwa [hAK i hi, hAs i hi] at this
  have hFl : liveCaseFunction Pr = Fl := by
    funext W Yt ωt bad b
    simp only [liveCaseFunction, hFldef, hPrdef]
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt
    · simp [hl]
    · simp only [hl, if_false]
      exact (Finset.prod_eq_zero hi₀ rfl).symm
  have hFm : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => Fl p.1 Yt p.2 bad b := fun Yt bad b =>
    Finset.measurable_fun_prod _ fun i hi => (hsz i hi).1 Yt bad b
  have hFg : IsGaugeInvariantCase Fl := by
    intro W Yt ωt bad b u hl h₁' h₂'
    exact Finset.prod_congr rfl fun i hi => (hsz i hi).2.1 W Yt ωt bad b u hl h₁' h₂'
  have hK0 : ∀ i, 0 ≤ 4 * (K.C₀ * ((lowerSites (f i)).card : ℝ)) := fun i => by positivity
  have hN := fun (J : Finset ι) (hJ : J ⊆ I) => hP₂ n G hG ι J (fun i => lowerSites (f i))
    (fun i hi => lowerSites_nonempty (hap'.nonempty i (hJ hi)))
    (fun i hi j hj hij => lowerSites_disjoint hap' i (hJ hi) j (hJ hj) hij)
  have hNm : ∀ (J : Finset ι) (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        ∏ i ∈ J, meanSiteScore (A i₀).score (lowerSites (f i)) Yt p.2 := fun J Yt _ _ =>
    Finset.measurable_fun_prod _ fun i _ => (measurable_meanSiteScore hs.borel _ Yt).comp measurable_snd
  have hNpos : ∀ (J : Finset ι) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      0 < ∏ i ∈ J, meanSiteScore (A i₀).score (lowerSites (f i)) Yt ωt := fun J Yt ωt =>
    Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (one_le_meanSiteScore hs.nonneg _ _ _)
  have hPrI : CaseIntegrable R G.cut G.coarse G.state Pr := by
    refine caseIntegrable_of_abs_le hnn (c := ∏ i ∈ I, (4 * (K.C₀ * ((lowerSites (f i)).card : ℝ))))
      (Finset.prod_nonneg fun i _ => hK0 i)
      (hN I subset_rfl).1 (fun _ Yt ωt _ _ => hNpos I Yt ωt) (hNm I) ?_ ?_
    · rw [hFl]
      exact hFm
    · intro W Yt ωt bad b hl _
      rw [hPrdef, Finset.abs_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi => hszb i hi W Yt ωt bad b hl
  have hFlI : CaseIntegrable R G.cut G.coarse G.state Fl := hFl ▸ caseIntegrable_liveCaseFunction hnn hPrI
  have hXp : ∀ i ∈ I, CaseIntegrable R G.cut G.coarse G.state (X i) := by
    intro i hi
    refine caseIntegrable_of_abs_le hnn (c := 4 * (K.C₀ * ((lowerSites (f i)).card : ℝ))) (hK0 i)
      (hN {i} (Finset.singleton_subset_iff.mpr hi)).1 (fun _ Yt ωt _ _ => hNpos {i} Yt ωt) (hNm {i})
      (hsz i hi).1 ?_
    intro W Yt ωt bad b hl _
    simpa using hszb i hi W Yt ωt bad b hl
  have hXI : ∀ i ∈ I, CaseIntegrable R G.cut G.coarse G.state (liveCaseFunction (X i)) :=
    fun i hi => caseIntegrable_liveCaseFunction hnn (hXp i hi)
  have m₁ : caseMean R G.cut G.coarse G.state Pr =
      G.expectation ∅ fun σ => settingMean (configSetting G σ) (G.badBondsOf σ) Fl := by
    rw [← caseMean_liveCaseFunction hnn, hFl]
    exact (hP₁.2 Fl hFm hFg hFlI).2
  have m₂ : ∀ i ∈ I, caseMean R G.cut G.coarse G.state (X i) = G.expectation ∅ (gasSupportMean (A i) G (f i)) := by
    intro i hi
    rw [← caseMean_liveCaseFunction hnn]
    exact (hP₁.2 _ ((hsz i hi).1) (hsz i hi).2.1 (hXI i hi)).2
  set pp : ℝ := (I.card : ℝ) with hpdef
  set Sm : ℝ := ∑ i ∈ I, ((lowerSites (f i)).card : ℝ) with hSm
  set Kp : ℝ := ∏ i ∈ I, (4 * (K.C₀ * ((lowerSites (f i)).card : ℝ))) with hKp
  set N' : ℝ := ∏ i ∈ I, meanSiteScore (coarseLabelScore K.s₁ (A i₀).score) (upperSites (f i)) G.state.1 G.state.2 with hN'
  have hrt : 0 < R.params.rt := by
    rw [hon.params_eq]
    exact hT.rt_pos
  have hSm1 : 1 ≤ Sm := by
    have h1 : ((lowerSites (f i₀)).card : ℝ) ≤ Sm :=
      Finset.single_le_sum (f := fun i => ((lowerSites (f i)).card : ℝ)) (fun i _ => by positivity) hi₀
    have h2 : 1 ≤ (lowerSites (f i₀)).card := Finset.card_pos.mpr (lowerSites_nonempty (hap'.nonempty i₀ hi₀))
    have h3 : (1 : ℝ) ≤ ((lowerSites (f i₀)).card : ℝ) := by exact_mod_cast h2
    linarith
  have hSm0 : 0 ≤ Sm := by linarith
  have hKp0 : 0 ≤ Kp := Finset.prod_nonneg fun i _ => hK0 i
  have hp0 : 0 ≤ pp := by positivity
  have hs' : ∀ w : CoarseLabel R.labels.Ω R.params.side, 0 ≤ coarseLabelScore K.s₁ (A i₀).score w := by
    have hs₁ : 0 ≤ K.s₁ := by
      have := htab'.admissible.params_admissible.s₁_eq
      have h4 : 0 ≤ (A i₀).responseParams.s₁ := by
        rw [this]
        positivity
      rwa [hK'] at h4
    rintro (u | st)
    · exact hs₁
    · simp only [coarseLabelScore]
      refine add_nonneg hs₁ (Finset.sum_nonneg fun o _ => ?_)
      rcases st.siteLabel o with u | a
      · simp
      · exact hs.nonneg a
  have hN'0 : 0 ≤ N' := Finset.prod_nonneg fun i _ => le_trans zero_le_one (one_le_meanSiteScore hs' _ _ _)
  set c₁ : ℝ := Ca * pp * Sm * Real.exp (-(R.params.rt * D / 2 ^ 4)) * Kp with hc₁
  have hc₁0 : 0 ≤ c₁ := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCa hp0) hSm0) (Real.exp_pos _).le) hKp0
  set P : G.Config → ℝ := fun σ => settingMean (configSetting G σ) (G.badBondsOf σ) Fl with hP
  set Mp : G.Config → ℝ := fun σ => ∏ i ∈ I, gasSupportMean (A i) G (f i) σ with hMp
  set Nσ : G.Config → ℝ := fun σ => ∏ i ∈ I, gasMeanSiteScore (A i₀) G (lowerSites (f i)) σ with hNσ
  set v : ι → ℝ := fun i => caseMean R ∅ (trivialField n) (emptyCoarseState R)
    (supportResponseSum (A i) (trivialField n) (f i)) with hvdef
  have hv : ∀ i ∈ I, |v i| ≤ (K.C₀ + 1 + 16 * R.params.coupling) *
      ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ) := by
    intro i hi
    have := h₉ y e₉ R (A i) (hAK i hi) (htab i hi) n hside.1 (f i) (hap'.norm_le i hi) (hap'.lower_norm_le i hi)
      (hap'.nonempty i hi)
    rw [hAK i hi] at this
    exact this
  have hae : ∀ᵐ σ ∂(G.gibbsLaw ∅), |P σ - Mp σ| ≤ c₁ * Nσ σ := by
    filter_upwards [hL.2.1.ae_admissible] with σ hσ
    have hset := h₈ y e₈ R hon hX' n G hG σ hσ
    have hball := (h₄ y e₄ R (A i₀) hK' htab' n (configSetting G σ) hside.1 hset).1
    have hFar := h₅ y e₅ R n (configSetting G σ) hside.1 hset (G.badBondsOf σ) ι I A f v D hAK htab hI hsize hlive hr h8 hap hv
    have eX : ∀ (i : ι) (η : FreeCoords (configSetting G σ).free), (configSetting G σ).InBalls η →
        liveCaseFunction (X i) ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
          (G.badBondsOf σ) (configSetting G σ).bases =
          supportResponseSum (A i) (configSetting G σ).coarse (f i) ((configSetting G σ).field η) (configSetting G σ).support
            (configSetting G σ).labelling (G.badBondsOf σ) (configSetting G σ).bases - v i := by
      intro i η hη
      unfold liveCaseFunction
      rw [if_pos (hball η hη).1]
      rfl
    have eP : P σ = weightedMean (chartDensity (configSetting G σ)) (fun η => ∏ i ∈ I,
        (supportResponseSum (A i) (configSetting G σ).coarse (f i) ((configSetting G σ).field η) (configSetting G σ).support
          (configSetting G σ).labelling (G.badBondsOf σ) (configSetting G σ).bases - v i)) :=
      weightedMean_congr_inBalls _ fun η hη => Finset.prod_congr rfl fun i _ => eX i η hη
    have eM : Mp σ = ∏ i ∈ I, weightedMean (chartDensity (configSetting G σ)) (fun η =>
        supportResponseSum (A i) (configSetting G σ).coarse (f i) ((configSetting G σ).field η) (configSetting G σ).support
          (configSetting G σ).labelling (G.badBondsOf σ) (configSetting G σ).bases - v i) :=
      Finset.prod_congr rfl fun i _ => weightedMean_congr_inBalls _ fun η hη => eX i η hη
    rw [eP, eM]
    refine hFar.trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib]
    have eN : ∏ i ∈ I, meanSiteScore (A i).score (weightSupportSites R.params.side R.depth (n * R.params.side) (f i))
        (configSetting G σ).support (configSetting G σ).labelling = Nσ σ :=
      Finset.prod_congr rfl fun i hi => by
        rw [hAs i hi]
        rfl
    rw [eN]
    show Ca * pp * Sm * Real.exp (-(R.params.rt * D / 2 ^ 4)) * (Kp * Nσ σ) = _
    rw [hc₁]
    ring
  obtain ⟨hMint, -, hBb⟩ := h₆ y e₆ R n G hG (A i₀).score ι I A f D hI hAK hAs htab hap'
  obtain ⟨-, hNint, hNle⟩ := hN I subset_rfl
  have hPm : AEStronglyMeasurable P (G.gibbsLaw ∅) := (hP₁.2 Fl hFm hFg hFlI).1.aestronglyMeasurable
  have hdiff : |G.expectation ∅ P - G.expectation ∅ Mp| ≤ c₁ * G.expectation ∅ Nσ :=
    (integrable_and_abs_integral_sub_le hPm hMint hNint hae).2
  have hε : Real.exp (pp * Real.exp (-(7 * T.gasRate * R.coupling))) ≤ Real.exp pp := by
    refine Real.exp_le_exp.mpr ?_
    have hch : 0 ≤ T.gasRate := by
      unfold ParameterAssignment.gasRate ParameterAssignment.κ₁
      have := hT.cE_pos
      have := hT.κ_pos
      have := hT.σ_pos
      positivity
    have : Real.exp (-(7 * T.gasRate * R.coupling)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hch hxpos.le])
    nlinarith
  have hpar : ∏ i ∈ I, meanSiteScore (coarseLabelScore (A i₀).responseParams.s₁ (A i₀).score)
      (parentBlocks (lowerSites (f i))) G.state.1 G.state.2 = N' := by
    exact Finset.prod_congr rfl fun i _ => by rw [parentBlocks_lowerSites, hK']
  rw [hpar] at hNle
  have hcp : (I.card : ℝ) = (p : ℝ) := by rw [hcard]
  refine ⟨hPrI, fun i hi => hXp i hi, ?_⟩
  rw [m₁, Finset.prod_congr rfl m₂]
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hrtD : 0 ≤ R.params.rt * D := by positivity
  have hgoal : ∏ i ∈ I, (4 * (K.C₀ * ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)) *
      meanSiteScore (coarseLabelScore K.s₁ (A i₀).score) (weightSupportSites R.params.side (R.depth + 1) n (f i))
        G.state.1 G.state.2) = Kp * N' :=
    Finset.prod_mul_distrib
  rw [hgoal, ← hcp]
  calc |G.expectation ∅ P - ∏ i ∈ I, G.expectation ∅ (gasSupportMean (A i) G (f i))|
      ≤ |G.expectation ∅ P - G.expectation ∅ Mp| +
          |G.expectation ∅ Mp - ∏ i ∈ I, G.expectation ∅ (gasSupportMean (A i) G (f i))| := abs_sub_le _ _ _
    _ ≤ c₁ * (Real.exp (pp * Real.exp (-(7 * T.gasRate * R.coupling))) * N') +
        Cb * pp ^ 2 * Real.exp (2 * pp) * Real.exp (-(R.params.rt * D / 2 ^ 7)) * Kp * N' :=
        add_le_add (hdiff.trans (mul_le_mul_of_nonneg_left hNle hc₁0)) hBb
    _ ≤ (Ca * pp * Real.exp pp + Cb * pp ^ 2 * Real.exp (2 * pp)) * Sm ^ 2 * Real.exp (-(R.params.rt * D / 2 ^ 7)) *
        (Kp * N') := by
        have h47 : R.params.rt * D / 2 ^ 7 ≤ R.params.rt * D / 2 ^ 4 :=
          div_le_div_of_nonneg_left hrtD (by norm_num) (by norm_num)
        rw [hc₁]
        exact two_term_bound hCa hCb hp0 hSm1 hKp0 hN'0 (Real.exp_pos _).le (Real.exp_pos _).le
          (Real.exp_le_exp.mpr (by linarith)) le_rfl hε
end TransfersOffTheWalk
end YangMills.Construction
end
