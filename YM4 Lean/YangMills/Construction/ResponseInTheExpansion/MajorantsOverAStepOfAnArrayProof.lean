import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsSmoothOffItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepAddUpProof
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ResponseInTheExpansion.MajorantsOfAStep
import YangMills.Construction.ResponseInTheExpansion.MajorantsOverAStepOfAnArray
import YangMills.Construction.ResponseInTheExpansion.MassOfAFunctionOverAStep
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ResponseInTheExpansion
open ClusterExpansionOfAStep StepSettings StepGas StepCosts RenormalizationStepParameters StepFloors TorusLumps TorusFields WeightedResponses ColdStepAtMirrorFrames
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markProduct_nonneg (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side))) : 0 ≤ markProduct R C V W bad := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.markProduct_nonneg <;> assumption
private theorem baseLaw_nonneg' (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) : 0 ≤ baseLaw (R := R) W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SmoothOffHull.baseLaw_nonneg_of_field <;> assumption
private theorem stepWeight_nonneg (hk : BondKernelProperties) (hR : R.IsWellPosed) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ωt bad b := by
  unfold stepWeight
  refine mul_nonneg (mul_nonneg (mul_nonneg (hR.hasExpansions.2.nonneg _ hside W Yt ωt hh) (baseLaw_nonneg' (R := R) W b)) ?_)
    (markProduct_nonneg hR C V W bad)
  exact Finset.prod_nonneg fun c _ => (hk.2 R.params R.coupling n _ _ b c).1.le
private theorem coarseStateMass_eq_sum (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) :
    coarseStateMass R C V q = ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n, configurationMass R C V bad Yt b q := rfl
private theorem coarseStateMass_measurable (hC : ConfigurationSupportedOnCoarseHull) (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n)
    (C : Finset (TorusSite n)) (V : TorusField n) (Y : Finset (TorusSite n)) :
    Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side => coarseStateMass R C V ⟨Y, ω⟩ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coarseStateMass_measurable <;> assumption
private theorem lintegral_coarseStateMass (hC : ConfigurationSupportedOnCoarseHull) (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n)
    (C : Finset (TorusSite n)) (V : TorusField n) (Y : Finset (TorusSite n)) :
    ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ ω, configurationMass R C V bad Yt b ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.lintegral_coarseStateMass <;> assumption
private theorem ae_coarseStateMass_lt_top (hC : ConfigurationSupportedOnCoarseHull) (hA : ConfigurationWeightsSum)
    (hH : CoarseHullIsHullState) (hR : R.IsWellPosed) (hside : IsBlockTorusSide R.params n) (V : TorusField n)
    (Y : Finset (TorusSite n)) (hY : (open Classical in Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V))) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side), coarseStateMass R (hotCoreSites R V) V ⟨Y, ω⟩ < ⊤ := by
  classical
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hside.2
  set C := hotCoreSites R V with hCdef
  have hcase : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
        ∫⁻ ω, configurationMass R C V bad Yt b ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
    intro bad Yt b
    have hmem : coarseHull R.params.side R.range R.nextRange bad Yt C ∈ Finset.univ.filter (IsHullState R.params R.nextRange V) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hH R.params hR.admissible R.range R.nextRange hR.range_le hR.nextRange_ge n hside.1 V bad Yt⟩
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · exact (hC R hR n hn C V bad Yt b).2.2
    · intro Y _ hY
      rw [lintegral_congr fun ω => (hC R hR n hn C V bad Yt b).1 ⟨Y, ω⟩ hY]
      simp
  have htotal : ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ENNReal.ofReal (kernelImage R.params R.coupling R.functional n V) := by
    simp_rw [lintegral_coarseStateMass hC hR hn C V]
    rw [← hA R hR n hn C V, Finset.sum_comm]
    refine Finset.sum_congr rfl fun bad _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => hcase bad Yt b
  have hfin : ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ htotal.le)
    exact Finset.single_le_sum (f := fun Y : Finset (TorusSite n) =>
      ∫⁻ ω, coarseStateMass R C V ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side))
      (fun _ _ => zero_le) hY
  exact ae_lt_top (coarseStateMass_measurable hC hR hn C V Y) hfin
private theorem coarseMassWith_ofReal_eq (hk : BondKernelProperties) (hR : R.IsWellPosed) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (P : (Yt : Finset (TorusSite (n * R.params.side))) → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ) (hP : ∀ Yt W ωt, 0 ≤ P Yt W ωt)
    (hI : CaseIntegrable R C V q (fun W Yt ωt _ _ => P Yt W ωt)) :
    coarseMassWith R C V (fun Yt W ωt => ENNReal.ofReal (P Yt W ωt)) q =
      ENNReal.ofReal (caseIntegral R C V q (fun W Yt ωt _ _ => P Yt W ωt)) := by
  classical
  have hnn : ∀ bad Yt b W ν, 0 ≤ caseTerm R C V q (fun W Yt ωt _ _ => P Yt W ωt) bad Yt b W ν := by
    intro bad Yt b W ν
    unfold caseTerm
    split_ifs with h
    · exact mul_nonneg (hP _ _ _) (stepWeight_nonneg hk hR hside C V _ Yt _ bad b h.1)
    · exact le_rfl
  have hterm : ∀ bad ∈ (markedBonds R C).powerset, ∀ Yt b, configurationMassWith R C V bad Yt b (fun W ωt => ENNReal.ofReal (P Yt W ωt)) q =
      ENNReal.ofReal (∫ W, ∫ ν : q.unlabelled Yt → R.labels.Ω, caseTerm R C V q (fun W Yt ωt _ _ => P Yt W ωt) bad Yt b W ν
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) := by
    intro bad hbad Yt b
    have hi := hI bad hbad Yt b
    rw [← integral_prod (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q (fun W Yt ωt _ _ => P Yt W ωt) bad Yt b p.1 p.2) hi,
      ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun p => hnn bad Yt b p.1 p.2),
      lintegral_prod _ hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
    unfold configurationMassWith
    refine lintegral_congr fun W => lintegral_congr fun ν => ?_
    unfold caseTerm
    by_cases h : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧ coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
    · rw [if_pos h, if_pos h, mul_comm (P _ _ _),
        ENNReal.ofReal_mul (stepWeight_nonneg hk hR hside C V _ Yt _ bad b h.1)]
    · rw [if_neg h, if_neg h, ENNReal.ofReal_zero]
  unfold coarseMassWith caseIntegral
  rw [ENNReal.ofReal_sum_of_nonneg fun bad _ => Finset.sum_nonneg fun Yt _ => Finset.sum_nonneg fun b _ =>
    integral_nonneg fun W => integral_nonneg fun ν => hnn bad Yt b W ν]
  refine Finset.sum_congr rfl fun bad hbad => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun Yt _ => Finset.sum_nonneg fun b _ =>
    integral_nonneg fun W => integral_nonneg fun ν => hnn bad Yt b W ν]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun b _ => integral_nonneg fun W => integral_nonneg fun ν => hnn bad Yt b W ν]
  exact Finset.sum_congr rfl fun b _ => hterm bad hbad Yt b
private theorem meanSiteScore_nonneg {m : ℕ} [NeZero m] {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (B Y : Finset (TorusSite m))
    (ω : Y → Ω) : 0 ≤ meanSiteScore s B Y ω := by
  classical
  unfold meanSiteScore
  refine add_nonneg zero_le_one (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun y _ => ?_))
  unfold siteScore
  split_ifs
  · exact hs _
  · exact le_rfl
private theorem meanSiteScore_measurable {m : ℕ} [NeZero m] {Ω : Type} [MeasurableSpace Ω] {s : Ω → ℝ} (hs : Measurable s)
    (B Y : Finset (TorusSite m)) : Measurable fun ω : Y → Ω => meanSiteScore s B Y ω := by
  classical
  unfold meanSiteScore
  refine measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun y _ => ?_))
  unfold siteScore
  by_cases hy : y ∈ Y
  · simp only [dif_pos hy]
    exact hs.comp (measurable_pi_apply _)
  · simp only [dif_neg hy]
    exact measurable_const
theorem stepMajorantBoundOfSymmetric_holds (hMaj : productMeanScoreStepBound) (hMass : massOverStepStatement)
    (hc : ConfigurationMassWithFunction) (hC : ConfigurationSupportedOnCoarseHull)
    (hA : ConfigurationWeightsSum) (hH : CoarseHullIsHullState) (hGr : HullStateIsHotCase)
    (hKill : CoarseWeightZeroOfFactorZero) (hFl : EventuallyFloorConditions) (hk : BondKernelProperties) :
    stepMajorantBoundOfSymmetric := by
  classical
  obtain ⟨rt₀, hrt, hM⟩ := hMaj
  refine ⟨rt₀, hrt, fun T hT hrtT K => ?_⟩
  obtain ⟨y₁, h₁⟩ := hM T hT hrtT K
  obtain ⟨y₂, h₂⟩ := hGr T hT
  have hLpos' : (0 : ℝ) < 2 ^ 40 * (T.side : ℝ) + 4 * (T.n₀ : ℝ) + 2 ^ 16 + 2 := by positivity
  obtain ⟨y₄, h₄⟩ := hFl T hT (2 ^ 40 * (T.side : ℝ) + 4 * (T.n₀ : ℝ) + 2 ^ 16 + 2) 1 hLpos' one_pos
  refine ⟨max (max y₁ y₂) (max y₄ (max T.floorMin 1)), fun y hy R A hK hA' => ?_⟩
  intro harr h x'' n _ hside ι I B hB
  have hy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy₂ : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy₄ : y₄ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy₅ : T.floorMin ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  have hy₆ : 1 ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  have hl := hA'.onFamily.params_eq
  have hp := hA'.onFamily.barrierFn_eq
  have hyx := hA'.onFamily.le_coupling
  have hfl := h₄ R.coupling (hy₄.trans hyx)
  obtain ⟨hxx, -, hr1, hr2⟩ := hfl.stable_nearby.2 R.nextCoupling hA'.abs_sub_le
  have hx1 : 1 ≤ R.coupling := hy₆.trans hyx
  have hrC : 2 ^ 40 * (T.side : ℝ) + 4 * (T.n₀ : ℝ) + 2 ^ 16 + 2 ≤ (clusterRange R.coupling : ℝ) := hfl.range_ge
  have hLL : R.params.side = T.side := by rw [hl]; rfl
  have hrN : 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 16 + 2 ≤ clusterRange R.coupling := by exact_mod_cast hrC
  have hn₀ : R.params.n₀ = T.n₀ := by rw [hl]; rfl
  have hadm : R.params.Admissible := by
    rw [hl]
    exact hT.fits y hy₅
  have hcut : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn := by
    have : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = T.threshold / 64
      rw [hl]
      rfl
    rw [this, hp]
    exact hT.cut
  have hR : R.IsWellPosed :=
    { hasExpansions := hA'.onFamily.isStep.1
      admissible := hadm
      isCutoff := hcut
      range_le := hr1
      nextRange_le := hr2
      nextRange_ge := by
        show 2 ^ 16 ≤ clusterRange R.nextCoupling
        omega
      range_ge_side := by
        show 2 ^ 40 * R.params.side ≤ clusterRange R.coupling
        rw [hLL]
        omega
      range_ge_base := by
        show 4 * R.params.n₀ + 2 ^ 16 ≤ clusterRange R.coupling
        rw [hn₀]
        omega
      coupling_pos := by linarith
      functional_spec := harr }
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hside.2
  have hsideL : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm R.params.side R.params.n₀]; exact Nat.mul_le_mul_right _ hn⟩
  have hsn := hA'.admissible.price.nonneg
  have hsb := hA'.admissible.price.borel
  set P : (Yt : Finset (TorusSite (n * R.params.side))) → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ :=
    fun Yt _ ωt => ∏ i ∈ I, meanSiteScore A.score (B i) Yt ωt with hPdef
  have hP0 : ∀ Yt W ωt, 0 ≤ P Yt W ωt := fun Yt W ωt => Finset.prod_nonneg fun i _ => meanSiteScore_nonneg hsn _ _ _
  have hPm : ∀ Yt : Finset (TorusSite (n * R.params.side)), Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => P Yt p.1 p.2 := fun Yt =>
    Finset.measurable_prod _ fun i _ => (meanSiteScore_measurable hsb (B i) Yt).comp measurable_snd
  have htower := hMass R hR n hside P hPm hP0
  set c : ℝ := Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling))) with hcdef
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  set P' : CoarseState R n → ℝ := fun q => ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
    (open Classical in (B i).image (parentBlock R.params.side)) q.1 q.2 with hP'def
  have hright : stateLIntegral (nextStepSetup R h T.lam x'') n (fun _ Y ω => ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
      (open Classical in (B i).image (parentBlock R.params.side)) Y ω) =
      ∫⁻ V, ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
        ∫⁻ ω, ENNReal.ofReal (coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ * P' ⟨Y, ω⟩)
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) ∂(fieldHaar n) := by
    unfold stateLIntegral
    refine lintegral_congr fun V => Finset.sum_congr rfl fun Y _ => lintegral_congr fun ω => ?_
    have e : (nextStepSetup R h T.lam x'').labelWeight n V Y ω = coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ :=
      dif_neg (NeZero.ne n)
    rw [e]
  have hleft : stateLIntegral R (n * R.params.side) (fun _ Y ω => ∏ i ∈ I, meanSiteScore A.score (B i) Y ω) =
      ∫⁻ V, ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
        ∫⁻ ω, coarseMassWith R (hotCoreSites R V) V (fun Yt W ωt => ENNReal.ofReal (P Yt W ωt)) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) ∂(fieldHaar n) := htower
  rw [hleft, hright, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun V => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun Y hY => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_coarseStateMass_lt_top hC hA hH hR hside V Y hY] with ω hω
  have hhull : IsHullState R.params R.nextRange V Y := (Finset.mem_filter.mp hY).2
  by_cases h0 : coarseStateMass R (hotCoreSites R V) V ⟨Y, ω⟩ = 0
  · have hz : coarseMassWith R (hotCoreSites R V) V (fun Yt W ωt => ENNReal.ofReal (P Yt W ωt)) ⟨Y, ω⟩ = 0 := by
      rw [coarseStateMass_eq_sum] at h0
      unfold coarseMassWith
      refine Finset.sum_eq_zero fun bad hbad => Finset.sum_eq_zero fun Yt hYt => Finset.sum_eq_zero fun b hb => ?_
      have h1 := (Finset.sum_eq_zero_iff.mp h0) bad hbad
      have h2 := (Finset.sum_eq_zero_iff.mp h1) Yt hYt
      have h3 := (Finset.sum_eq_zero_iff.mp h2) b hb
      exact (hc R hR n hn (hotCoreSites R V) V bad Yt b _ ((ENNReal.measurable_ofReal).comp (hPm Yt))).2.1 ⟨Y, ω⟩ h3
    rw [hz]
    exact zero_le
  · have hpos : 0 < coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ := ENNReal.toReal_pos h0 hω.ne
    have hphi : ∀ X ∈ chainComponents R.nextRange (⟨Y, ω⟩ : CoarseState R n).1, coarseFactor V (⟨Y, ω⟩ : CoarseState R n) X ≠ 0 := by
      intro X hX hz
      have := hKill R hR n hside V ⟨Y, ω⟩ hhull ⟨X, hX, hz⟩
      exact hpos.ne' this
    have hHot : (hotCaseGround R V (⟨Y, ω⟩ : CoarseState R n)).IsHotCase :=
      h₂ y hy₂ R hA'.onFamily hR n hside V ⟨Y, ω⟩ hhull hphi
    obtain ⟨hint, hmean⟩ := h₁ y hy₁ R A hK hA' n (hotCaseGround R V ⟨Y, ω⟩) (Or.inr hHot) ι I B hB
    have hlink := coarseMassWith_ofReal_eq hk hR hsideL (hotCoreSites R V) V ⟨Y, ω⟩ P hP0 hint
    rw [hlink]
    have hle : caseIntegral R (hotCoreSites R V) V ⟨Y, ω⟩ (fun W Yt ωt _ _ => P Yt W ωt) ≤
        c * (coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ * P' ⟨Y, ω⟩) := by
      have h1 := (div_le_iff₀ hpos).mp hmean
      calc caseIntegral R (hotCoreSites R V) V ⟨Y, ω⟩ (fun W Yt ωt _ _ => P Yt W ωt)
          ≤ c * P' ⟨Y, ω⟩ * coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ := h1
        _ = c * (coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ * P' ⟨Y, ω⟩) := by ring
    calc ENNReal.ofReal (caseIntegral R (hotCoreSites R V) V ⟨Y, ω⟩ (fun W Yt ωt _ _ => P Yt W ωt))
        ≤ ENNReal.ofReal (c * (coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ * P' ⟨Y, ω⟩)) := ENNReal.ofReal_le_ofReal hle
      _ = _ := ENNReal.ofReal_mul hc0
end YangMills.Construction.ResponseInTheExpansion
end
