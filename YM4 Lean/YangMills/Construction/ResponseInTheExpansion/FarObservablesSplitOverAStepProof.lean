import YangMills.Construction.ResponseInTheExpansion.FarObservablesSplitInASetting
import YangMills.Construction.ResponseInTheExpansion.FarObservablesSplitOverAStep
import YangMills.Construction.ResponseInTheExpansion.FarObservablesSplitOverTheGas
import YangMills.Construction.ResponseInTheExpansion.VariablesOfFarObservablesHaveTheirSizes
import YangMills.Construction.TransfersOffTheWalk.OneStepOfSeveralResponsesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open Dobrushin
namespace ResponseInTheExpansion
open WeightedResponses StepSettings RenormalizationStepParameters StepGas StepCosts TorusFields TorusLumps FreeEnergies StateMeasurability
section Cases
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem caseTerm_liveCaseFunction
    (hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      IsHullState R.params R.range W Yt → 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt)
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) (F : CaseFunction R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V q (liveCaseFunction F) bad Yt b W ν = caseTerm R C V q F bad Yt b W ν := by apply _root_.YangMills.SharedProofs.p99396 <;> assumption
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
    Measurable fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν := by apply _root_.YangMills.SharedProofs.p55409 <;> assumption
private theorem caseIntegrable_of_abs_le_mul
    (hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      IsHullState R.params R.range W Yt → 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt)
    {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n} {F H : CaseFunction R n} {c : ℝ}
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
  have heq : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q F bad Yt b p.1 p.2) =
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
      have hbases : b ∈ baseChoices R.params
          (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks p.1)) := by
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
private theorem lowerSites_disjoint {ι : Type} {I : Finset ι}
    {f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} {D : ℕ}
    (h : SeparatedWeights I f D) : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (lowerSites (f i)) (lowerSites (f j)) := by
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
    (Y : Finset (TorusSite m)) (y : TorusSite m) : Measurable fun ω : Y → Ω => siteScore s Y ω y := by apply _root_.YangMills.SharedProofs.p56706 <;> assumption
private theorem measurable_meanSiteScore {Ω : Type} [MeasurableSpace Ω] {s : Ω → ℝ} (hs : Measurable s) {m : ℕ}
    [NeZero m] (B Y : Finset (TorusSite m)) : Measurable fun ω : Y → Ω => meanSiteScore s B Y ω := by
  unfold meanSiteScore
  exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun y _ => measurable_siteScore hs Y y))
private theorem one_le_meanSiteScore {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {m : ℕ} [NeZero m]
    (B Y : Finset (TorusSite m)) (ω : Y → Ω) : 1 ≤ meanSiteScore s B Y ω := by apply _root_.YangMills.SharedProofs.p45452 <;> assumption
end Sites
private theorem add_le_combined_bound {Ca Cb p S K N' d₁ d₂ ε : ℝ} (hCa : 0 ≤ Ca) (hp : 1 ≤ p)
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hN : 0 ≤ N') (hd₁ : 0 ≤ d₁) (h₁ : d₁ ≤ d₂) (hε : 0 ≤ ε) :
    Ca * p * S * d₁ * K * (Real.exp (p * ε) * N') + Cb * p ^ 2 * Real.exp (2 * p * ε) * S * d₂ * (K * N') ≤
      (Ca + Cb) * p ^ 2 * Real.exp (2 * p * ε) * S * d₂ * (K * N') := by
  have hpp : p ≤ p ^ 2 := by nlinarith
  have he : Real.exp (p * ε) ≤ Real.exp (2 * p * ε) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p) hε])
  calc Ca * p * S * d₁ * K * (Real.exp (p * ε) * N') + Cb * p ^ 2 * Real.exp (2 * p * ε) * S * d₂ * (K * N')
      = Ca * (p * Real.exp (p * ε) * d₁) * (S * (K * N')) +
          Cb * p ^ 2 * Real.exp (2 * p * ε) * S * d₂ * (K * N') := by ring
    _ ≤ Ca * (p ^ 2 * Real.exp (2 * p * ε) * d₂) * (S * (K * N')) +
          Cb * p ^ 2 * Real.exp (2 * p * ε) * S * d₂ * (K * N') := by gcongr
    _ = _ := by ring
private theorem integrable_and_abs_integral_sub_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {P Mp N : Ω → ℝ}
    {c : ℝ} (hP : AEStronglyMeasurable P μ) (hM : Integrable Mp μ) (hN : Integrable N μ)
    (hae : ∀ᵐ σ ∂μ, |P σ - Mp σ| ≤ c * N σ) :
    Integrable P μ ∧ |∫ σ, P σ ∂μ - ∫ σ, Mp σ ∂μ| ≤ c * ∫ σ, N σ ∂μ := by apply _root_.YangMills.SharedProofs.p39813 <;> assumption
set_option maxHeartbeats 1000000 in
theorem separatedProductOverStep_proof (hCase : caseMeanEqGasMeanStatement) (hScores : gasMeanScoreProductBound)
    (hSizes : centeredSupportResponseBounds)
    (hA : separatedProductInChartStatement) (hB : separatedProductOverGasStatement)
    (hWeight : ClusterExpansionOfAStep.GasIsActivityBounded) (hLaws : ActivityConditionalLawsStatement)
    (hCfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) : separatedProductOverStepStatement := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hCase
  obtain ⟨r₂, p₂, H₂⟩ := hScores
  obtain ⟨r₃, p₃, H₃⟩ := hSizes
  obtain ⟨r₅, p₅, H₅⟩ := hA
  obtain ⟨r₆, p₆, H₆⟩ := hB
  obtain ⟨r₇, p₇, H₇⟩ := hWeight
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₅ c) (min (r₆ c) (r₇ c))))), fun c => ?_, ?_⟩
  · simp only [lt_min_iff]
    exact ⟨p₁ c, p₂ c, p₃ c, p₅ c, p₆ c, p₇ c⟩
  intro T hT hle K
  simp only [le_min_iff] at hle
  obtain ⟨l₁, l₂, l₃, l₅, l₆, l₇⟩ := hle
  obtain ⟨y₁, h₁⟩ := H₁ T hT l₁
  obtain ⟨y₂, h₂⟩ := H₂ T hT l₂ K
  obtain ⟨y₃, h₃⟩ := H₃ T hT l₃ K
  obtain ⟨y₅, Ca, hCa, h₅⟩ := H₅ T hT l₅ K
  obtain ⟨y₆, Cb, hCb, h₆⟩ := H₆ T hT l₆ K
  obtain ⟨y₇, h₇⟩ := H₇ T hT l₇
  obtain ⟨y₈, h₈⟩ := hCfg T hT
  refine ⟨max y₁ (max y₂ (max y₃ (max y₅ (max y₆ (max y₇ (max y₈ (200 * T.B))))))), Ca + Cb,
    add_nonneg hCa hCb, fun y hy => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨e₁, e₂, e₃, e₅, e₆, e₇, e₈, e₉⟩ := hy
  have hPa := h₅ y e₅
  have hPb := h₆ y e₆
  intro R A hAK htab n _ G hG ι I f D hI hap
  have hon := htab.onFamily
  have hrow : R.HasExpansions := hon.isStep.1
  have hLpos : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hside : R.params.n₀ ≤ n ∧ IsBlockTorusSide R.params (n * R.params.side) := by
    rcases hG with hc | hh
    · exact ⟨hc.n₀_le, Dvd.intro_left n rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hc.n₀_le⟩
    · have h₂ := hh.isBlockSide.2
      have h₃ : R.params.n₀ ≤ R.params.side * R.params.n₀ := Nat.le_mul_of_pos_left _ (by omega)
      exact ⟨h₃.trans h₂, Dvd.intro_left n rfl, h₂.trans (Nat.le_mul_of_pos_right _ (by omega))⟩
  have hnn : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω), IsHullState R.params R.range W Yt →
      0 ≤ R.labelWeight (n * R.params.side) W Yt ωt := fun W Yt ωt h => hrow.2.nonneg _ hside.2 W Yt ωt h
  have hs := htab.admissible.price
  have hB₁ : 1 ≤ T.B := hT.B_ge
  have hxy : y ≤ R.coupling := hon.le_coupling
  have hX' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have := (abs_le.mp htab.abs_sub_le).2
    linarith
  have hxpos : 0 < R.coupling := by linarith
  have hP₁ := h₁ y e₁ R hon hX' n G hG
  have hP₂ := h₂ y e₂ R A hAK htab
  have hP₃ := h₃ y e₃ R A hAK htab
  have hW := h₇ y e₇ R hon hX' n G hG (fun j => j.1.Touches ∅)
  have hL := hLaws G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasureOff fun j => j.1.Touches ∅) G.weight _ hW
  have : IsProbabilityMeasure (G.gibbsLaw ∅) := hL.1
  have hC₀ : 0 ≤ A.responseParams.C₀ := by
    have := htab.admissible.params_admissible
    have ha : 1 ≤ R.params.coupling := by
      rw [hon.params_eq]
      exact hT.a_ge
    have h1 := this.C₀_eq
    have h2 := this.N₀_nonneg
    have h3 := this.Kc_ge
    rw [h1]
    linarith
  set X : ι → CaseFunction R n := fun i => centeredSupportResponse A G.coarse (f i) with hXdef
  set Fl : CaseFunction R n := fun W Yt ωt bad b => ∏ i ∈ I, liveCaseFunction (X i) W Yt ωt bad b with hFldef
  set Pr : CaseFunction R n := fun W Yt ωt bad b => ∏ i ∈ I, X i W Yt ωt bad b with hPrdef
  have hsz := fun i (hi : i ∈ I) => hP₃ n hside.1 G.coarse (f i) (hap.weightNorm_le i hi) (hap.nonempty i hi)
  have hFl : liveCaseFunction Pr = Fl := by
    funext W Yt ωt bad b
    simp only [liveCaseFunction, hFldef, hPrdef]
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt
    · simp [hl]
    · obtain ⟨i, hi⟩ := hI
      simp only [hl, if_false]
      exact (Finset.prod_eq_zero hi rfl).symm
  have hFm : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => Fl p.1 Yt p.2 bad b :=
    fun Yt bad b => Finset.measurable_fun_prod _ fun i hi => (hsz i hi).1 Yt bad b
  have hFg : IsGaugeInvariantCase Fl := by
    intro W Yt ωt bad b u hl h₁' h₂'
    exact Finset.prod_congr rfl fun i hi => (hsz i hi).2.1 W Yt ωt bad b u hl h₁' h₂'
  have hK0 : ∀ i, 0 ≤ 4 * lowerSizeConst A (f i) := fun i => by
    unfold lowerSizeConst
    positivity
  have hN := fun (J : Finset ι) (hJ : J ⊆ I) => hP₂ n G hG ι J (fun i => lowerSites (f i))
    (fun i hi => lowerSites_nonempty (hap.nonempty i (hJ hi)))
    (fun i hi j hj hij => lowerSites_disjoint hap i (hJ hi) j (hJ hj) hij)
  have hNm : ∀ (J : Finset ι) (Yt : Finset (TorusSite (n * R.params.side)))
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        ∏ i ∈ J, meanSiteScore A.score (lowerSites (f i)) Yt p.2 := fun J Yt _ _ =>
    Finset.measurable_fun_prod _ fun i _ => (measurable_meanSiteScore hs.borel _ Yt).comp measurable_snd
  have hNpos : ∀ (J : Finset ι) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      0 < ∏ i ∈ J, meanSiteScore A.score (lowerSites (f i)) Yt ωt := fun J Yt ωt =>
    Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (one_le_meanSiteScore hs.nonneg _ _ _)
  have hPrI : CaseIntegrable R G.cut G.coarse G.state Pr := by
    refine caseIntegrable_of_abs_le_mul hnn (c := ∏ i ∈ I, (4 * lowerSizeConst A (f i)))
      (hN I subset_rfl).1 (fun _ Yt ωt _ _ => hNpos I Yt ωt) (hNm I) ?_ ?_
    · rw [hFl]
      exact hFm
    · intro W Yt ωt bad b hl _
      rw [hPrdef, Finset.abs_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi => (hsz i hi).2.2 W Yt ωt bad b hl
  have hFlI : CaseIntegrable R G.cut G.coarse G.state Fl := hFl ▸ caseIntegrable_liveCaseFunction hnn hPrI
  have hXI : ∀ i ∈ I, CaseIntegrable R G.cut G.coarse G.state (liveCaseFunction (X i)) := by
    intro i hi
    refine caseIntegrable_liveCaseFunction hnn ?_
    refine caseIntegrable_of_abs_le_mul hnn (c := 4 * lowerSizeConst A (f i))
      (hN {i} (Finset.singleton_subset_iff.mpr hi)).1 (fun _ Yt ωt _ _ => hNpos {i} Yt ωt) (hNm {i})
      (hsz i hi).1 ?_
    intro W Yt ωt bad b hl _
    simpa using (hsz i hi).2.2 W Yt ωt bad b hl
  have m₁ : caseMean R G.cut G.coarse G.state Pr =
      G.expectation ∅ fun σ => settingMean (configSetting G σ) (G.badBondsOf σ) Fl := by
    rw [← caseMean_liveCaseFunction hnn, hFl]
    exact (hP₁.2 Fl hFm hFg hFlI).2
  have m₂ : ∀ i ∈ I, caseMean R G.cut G.coarse G.state (X i) = G.expectation ∅ (gasSupportMean A G (f i)) := by
    intro i hi
    rw [← caseMean_liveCaseFunction hnn]
    exact (hP₁.2 _ ((hsz i hi).1) (hsz i hi).2.1 (hXI i hi)).2
  set p : ℝ := (I.card : ℝ) with hpdef
  set Sm : ℝ := ∑ i ∈ I, ((lowerSites (f i)).card : ℝ) with hSm
  set Kp : ℝ := ∏ i ∈ I, (4 * lowerSizeConst A (f i)) with hKp
  set N' : ℝ := ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites (f i))
    G.state.1 G.state.2 with hN'
  have hrt : 0 < R.params.rt := by
    rw [hon.params_eq]
    exact hT.rt_pos
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun i _ => by positivity
  have hKp0 : 0 ≤ Kp := Finset.prod_nonneg fun i _ => hK0 i
  have hp0 : 0 ≤ p := by positivity
  have hs' : ∀ w : CoarseLabel R.labels.Ω R.params.side, 0 ≤ coarseLabelScore A.responseParams.s₁ A.score w := by
    have hs₁ : 0 ≤ A.responseParams.s₁ := by
      have := htab.admissible.params_admissible.s₁_eq
      have ha : 1 ≤ R.params.coupling := by
        rw [hon.params_eq]
        exact hT.a_ge
      rw [this]
      positivity
    rintro (u | st)
    · exact hs₁
    · simp only [coarseLabelScore]
      refine add_nonneg hs₁ (Finset.sum_nonneg fun o _ => ?_)
      rcases st.siteLabel o with u | a
      · simp
      · exact hs.nonneg a
  have hN'0 : 0 ≤ N' := Finset.prod_nonneg fun i _ => le_trans zero_le_one (one_le_meanSiteScore hs' _ _ _)
  set c₁ : ℝ := Ca * p * Sm * Real.exp (-(R.params.rt * D / 2 ^ 4)) * Kp with hc₁
  have hc₁0 : 0 ≤ c₁ := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCa hp0) hSm0) (Real.exp_pos _).le) hKp0
  set P : G.Config → ℝ := fun σ => settingMean (configSetting G σ) (G.badBondsOf σ) Fl with hP
  set Mp : G.Config → ℝ := fun σ => ∏ i ∈ I, gasSupportMean A G (f i) σ with hMp
  set Nσ : G.Config → ℝ := fun σ => ∏ i ∈ I, gasMeanSiteScore A G (lowerSites (f i)) σ with hNσ
  have hae : ∀ᵐ σ ∂(G.gibbsLaw ∅), |P σ - Mp σ| ≤ c₁ * Nσ σ := by
    filter_upwards [hL.2.1.ae_admissible] with σ hσ
    have hset := h₈ y e₈ R hon hX' n G hG σ hσ
    have hbound := hPa R A hAK htab n (configSetting G σ) hside.1 hset (G.badBondsOf σ) ι I f D hI hap
    have hprod : ∏ i ∈ I, lowerMajorant A (f i) (configSetting G σ).support (configSetting G σ).labelling =
        Kp * Nσ σ := by
      simp only [lowerMajorant, Finset.prod_mul_distrib, hKp, hNσ, gasMeanSiteScore]
    rw [hprod] at hbound
    calc |P σ - Mp σ| ≤ _ := hbound
      _ = c₁ * Nσ σ := by
        simp only [hc₁, hpdef, hSm, totalLowerSites]
        ring
  obtain ⟨hMint, -, hBb⟩ := hPb R A hAK htab n G hG ι I f D hI hap
  obtain ⟨-, hNint, hNle⟩ := hN I subset_rfl
  have hPm : AEStronglyMeasurable P (G.gibbsLaw ∅) := (hP₁.2 Fl hFm hFg hFlI).1.aestronglyMeasurable
  have hdiff : |G.expectation ∅ P - G.expectation ∅ Mp| ≤ c₁ * G.expectation ∅ Nσ :=
    (integrable_and_abs_integral_sub_le hPm hMint hNint hae).2
  have hpar : ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks (lowerSites (f i)))
      G.state.1 G.state.2 = N' := by
    exact Finset.prod_congr rfl fun i _ => by rw [parentBlocks_lowerSites]
  rw [hpar] at hNle
  have hMN : ∏ i ∈ I, upperMajorant A G (f i) = Kp * N' := by
    simp only [upperMajorant, Finset.prod_mul_distrib, hKp, hN']
  have hch : 0 ≤ T.gasRate := by
    unfold ParameterAssignment.gasRate ParameterAssignment.κ₁
    have := hT.cE_pos
    have := hT.κ_pos
    have := hT.σ_pos
    positivity
  have hp1 : 1 ≤ p := by
    rw [hpdef]
    exact_mod_cast hI.card_pos
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hrtD : 0 ≤ R.params.rt * D := by positivity
  refine ⟨hPrI, ?_⟩
  rw [m₁, Finset.prod_congr rfl m₂, hMN]
  rw [hMN] at hBb
  have hSt : totalLowerSites I f = Sm := rfl
  rw [hSt] at hBb ⊢
  calc |G.expectation ∅ P - ∏ i ∈ I, G.expectation ∅ (gasSupportMean A G (f i))|
      ≤ |G.expectation ∅ P - G.expectation ∅ Mp| +
          |G.expectation ∅ Mp - ∏ i ∈ I, G.expectation ∅ (gasSupportMean A G (f i))| := abs_sub_le _ _ _
    _ ≤ c₁ * (Real.exp (p * Real.exp (-(7 * T.gasRate * R.coupling))) * N') +
        Cb * p ^ 2 * Real.exp (2 * p * Real.exp (-(7 * T.gasRate * R.coupling))) * Sm *
          Real.exp (-(R.params.rt * D / 2 ^ 6)) * (Kp * N') :=
        add_le_add (hdiff.trans (mul_le_mul_of_nonneg_left hNle hc₁0)) hBb
    _ ≤ (Ca + Cb) * p ^ 2 * Real.exp (2 * p * Real.exp (-(7 * T.gasRate * R.coupling))) * Sm *
          Real.exp (-(R.params.rt * D / 2 ^ 6)) * (Kp * N') :=
        add_le_combined_bound hCa hp1 hSm0 hKp0 hN'0 (Real.exp_pos _).le
          (Real.exp_le_exp.mpr (by
            have h₂ : R.params.rt * D / 2 ^ 6 ≤ R.params.rt * D / 2 ^ 4 :=
              div_le_div_of_nonneg_left hrtD (by norm_num) (by norm_num)
            linarith)) (Real.exp_pos _).le
end ResponseInTheExpansion
end YangMills.Construction
end
