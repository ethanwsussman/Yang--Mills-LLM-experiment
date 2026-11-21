import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeight
import YangMills.Construction.ResponseInTheExpansion.ResponseIsTheIntegralOfItsCases
import YangMills.Construction.SixteenPointsOnASmallTorus.CentringIsTheSumOfTheShiftsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepGas StepCosts BlockAverages BlockPlaces ClusterExpansionOfAStep ResponseInTheExpansion
section PositiveAndNegativeParts
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
private theorem enorm_eq_ofReal_add_ofReal_neg (a : ℝ) : ‖a‖ₑ = ENNReal.ofReal a + ENNReal.ofReal (-a) := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -a ≤ 0), add_zero]
  · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
private theorem eq_toReal_ofReal_sub_toReal_ofReal_neg (a : ℝ) :
    a = (ENNReal.ofReal a).toReal - (ENNReal.ofReal (-a)).toReal := by
  rcases le_total 0 a with h | h
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -a ≤ 0), ENNReal.toReal_ofReal h]
    simp
  · rw [ENNReal.ofReal_of_nonpos h, ENNReal.toReal_ofReal (by linarith : 0 ≤ -a)]
    simp
private theorem integrable_and_iterated_integral_eq (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (h : X → Y → ℝ)
    (hm : Measurable (Function.uncurry h))
    (hp : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (h x y) ∂ν ∂μ ≠ ⊤)
    (hn : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (-h x y) ∂ν ∂μ ≠ ⊤) :
    Integrable (Function.uncurry h) (μ.prod ν) ∧
      ∫ x, ∫ y, h x y ∂ν ∂μ =
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal (h x y) ∂ν ∂μ).toReal -
          (∫⁻ x, ∫⁻ y, ENNReal.ofReal (-h x y) ∂ν ∂μ).toReal := by
  have mp : Measurable fun p : X × Y => ENNReal.ofReal (Function.uncurry h p) := hm.ennreal_ofReal
  have mn : Measurable fun p : X × Y => ENNReal.ofReal (-Function.uncurry h p) := hm.neg.ennreal_ofReal
  have lp : ∫⁻ p, ENNReal.ofReal (Function.uncurry h p) ∂(μ.prod ν) =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (h x y) ∂ν ∂μ := lintegral_prod _ mp.aemeasurable
  have ln : ∫⁻ p, ENNReal.ofReal (-Function.uncurry h p) ∂(μ.prod ν) =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (-h x y) ∂ν ∂μ := lintegral_prod _ mn.aemeasurable
  have hi : Integrable (Function.uncurry h) (μ.prod ν) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [enorm_eq_ofReal_add_ofReal_neg]
    rw [lintegral_add_left mp, lp, ln]
    exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hp, lt_top_iff_ne_top.mpr hn⟩
  refine ⟨hi, ?_⟩
  have e : ∫ x, ∫ y, h x y ∂ν ∂μ = ∫ p, Function.uncurry h p ∂(μ.prod ν) := (integral_prod _ hi).symm
  rw [e, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, lp, ln]
end PositiveAndNegativeParts
section CoarseStates
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem fieldWithStoredLinks_of_linkValue (q : CoarseState R n) {y : TorusSite n}
    {s : BlockLabels R.labels.Ω R.params.side}
    (hs : q.markAt y = some s) (o : BlockOffset R.params.side) (i : Fin 4) {g : UnitQuaternion}
    (hf : s.linkValue (o, i) = Sum.inr g)
    (W : TorusField (n * R.params.side)) : q.fieldWithStoredLinks W (blockSite y o) i = g := by
  simp only [CoarseState.fieldWithStoredLinks]
  rw [parentBlock_blockSite, hs]
  simp [siteOffset_blockSite, hf]
private theorem measurable_fieldWithStoredLinks (q : CoarseState R n) :
    Measurable fun W : TorusField (n * R.params.side) => q.fieldWithStoredLinks W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν := by
  classical
  refine measurable_pi_lambda _ fun z => ?_
  obtain ⟨z, hz⟩ := z
  by_cases h : z ∈ q.labelSet
  · simp_rw [fillLabels_of_mem q Yt _ z hz h]
    exact measurable_const
  · have hr : z ∈ q.unlabelled Yt := by
      rw [unlabelled_eq_sdiff]
      exact Finset.mem_sdiff.mpr ⟨hz, h⟩
    simp_rw [fillLabels_of_mem_unlabelled q Yt _ z hz hr]
    exact measurable_pi_apply _
private theorem coarseStateOf_fill_stable (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (q : CoarseState R n)
    {W₀ W : TorusField (n * R.params.side)} {ν₀ ν : q.unlabelled Yt → R.labels.Ω}
    (h : coarseStateOf R C (q.fieldWithStoredLinks W₀) Yt (q.fillLabels Yt ν₀) bad b = q) :
    coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q := by
  classical
  refine Eq.trans ?_ h
  refine congrArg (Sigma.mk _) (funext fun y => ?_)
  by_cases hy : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C
  · rw [if_pos hy, if_pos hy]
    congr 1
    have hs : q.markAt y = some (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C)
        (q.fieldWithStoredLinks W₀) Yt (q.fillLabels Yt ν₀) bad b y) := by
      have h1 : (coarseStateOf R C (q.fieldWithStoredLinks W₀) Yt (q.fillLabels Yt ν₀) bad b).markAt y =
          some (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) (q.fieldWithStoredLinks W₀) Yt
            (q.fillLabels Yt ν₀) bad b y) := by
        refine markAt_of_inr (q := coarseStateOf R C (q.fieldWithStoredLinks W₀) Yt (q.fillLabels Yt ν₀) bad b)
          y.2 ?_
        show (if (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C then _ else _) = _
        rw [if_pos hy]
      rwa [h] at h1
    refine blockConfig_ext rfl rfl ?_ rfl ?_
    · funext o
      simp only [blockConfigAt]
      by_cases ho : blockSite (y : TorusSite n) o ∈ Yt
      · rw [dif_pos ho, dif_pos ho]
        have h3 : q.labelAt (blockSite (y : TorusSite n) o) = Sum.inr (q.fillLabels Yt ν₀ ⟨_, ho⟩) := by
          rw [labelAt_blockSite hs]
          simp only [blockConfigAt]
          rw [dif_pos ho]
        have hz : blockSite (y : TorusSite n) o ∈ q.labelSet := mem_labelSet.mpr (by rw [h3]; simp)
        rw [fillLabels_of_mem q Yt ν _ ho hz, fillLabels_of_mem q Yt ν₀ _ ho hz]
      · rw [dif_neg ho, dif_neg ho]
    · funext c
      simp only [blockConfigAt]
      by_cases hc : parentBlock R.params.side
          (blockSite (L := R.params.side) (y : TorusSite n) c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈
          storedBlocks R.params.side R.range bad Yt C
      · rw [if_pos hc, if_pos hc]
        have hf : (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) (q.fieldWithStoredLinks W₀) Yt
            (q.fillLabels Yt ν₀) bad b y).linkValue
            (c.1, c.2) = Sum.inr (q.fieldWithStoredLinks W₀ (blockSite (y : TorusSite n) c.1) c.2) := by
          simp only [blockConfigAt]
          rw [if_pos hc]
        rw [fieldWithStoredLinks_of_linkValue q hs c.1 c.2 hf W]
      · rw [if_neg hc, if_neg hc]
  · rw [if_neg hy, if_neg hy]
open Classical in
private def stateMassTerm (R : StepSetup) (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal)
    (q : CoarseState R n) (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) : ENNReal :=
  if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
    ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) *
      g (q.fieldWithStoredLinks W) (q.fillLabels Yt ν) else 0
private theorem measurable_stateMassTerm (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (hw : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      configurationWeight R C V bad Yt b p.1 p.2)
    (g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal)
    (hg : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => g p.1 p.2)
    (q : CoarseState R n) :
    Measurable (Function.uncurry (stateMassTerm R C V bad Yt b g q)) := by
  classical
  by_cases hex : ∃ (W₀ : TorusField (n * R.params.side)) (ν₀ : q.unlabelled Yt → R.labels.Ω),
      coarseStateOf R C (q.fieldWithStoredLinks W₀) Yt (q.fillLabels Yt ν₀) bad b = q
  · obtain ⟨W₀, ν₀, h₀⟩ := hex
    have hm : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) :=
      ((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk
        ((measurable_fillLabels q Yt).comp measurable_snd)
    have e : Function.uncurry (stateMassTerm R C V bad Yt b g q) = fun p =>
        configurationWeight R C V bad Yt b (q.fieldWithStoredLinks p.1) (q.fillLabels Yt p.2) *
          g (q.fieldWithStoredLinks p.1) (q.fillLabels Yt p.2) := by
      funext p
      have hst := coarseStateOf_fill_stable C bad Yt b q (W := p.1) (ν := p.2) h₀
      simp only [Function.uncurry, stateMassTerm, configurationWeight]
      by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks p.1) Yt
      · rw [if_pos ⟨hh, hst⟩, if_pos hh]
      · rw [if_neg fun h => hh h.1, if_neg hh, zero_mul]
    rw [e]
    exact (hw.comp hm).mul (hg.comp hm)
  · have e : Function.uncurry (stateMassTerm R C V bad Yt b g q) = fun _ => 0 := by
      funext p
      simp only [Function.uncurry, stateMassTerm]
      exact if_neg fun h => hex ⟨p.1, p.2, h.2⟩
    rw [e]
    exact measurable_const
end CoarseStates
section StepWeights
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem bondMark_bounds (hR : R.IsWellPosed) (V : TorusField n) (W : TorusField (n * R.params.side))
    (c : TorusBond (n * R.params.side)) :
    0 ≤ bondMark R V W c ∧ bondMark R V W c ≤ 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.bondMark_nonneg_le_one <;> assumption
private theorem markProduct_bounds (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side))) : 0 ≤ markProduct R C V W bad ∧ markProduct R C V W bad ≤ 1 := by
  classical
  unfold markProduct
  refine ⟨Finset.prod_nonneg fun c _ => ?_, Finset.prod_le_one (fun c _ => ?_) fun c _ => ?_⟩ <;>
    · have := bondMark_bounds hR V W c
      split_ifs <;> linarith [this.1, this.2]
private theorem sum_markProduct (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side)) :
    ∑ bad ∈ (markedBonds R C).powerset, markProduct R C V W bad = 1 := by apply _root_.YangMills.SharedProofs.p20431 <;> assumption
private def baseKernelLaw (R : StepSetup) (V : TorusField n) (W : TorusField (n * R.params.side))
    (b : BaseChoice R.params.side n) : ℝ :=
  baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
    bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
      (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c
private theorem baseKernelLaw_eq (V : TorusField n) (W : TorusField (n * R.params.side))
    (b : BaseChoice R.params.side n) :
    baseKernelLaw R V W b = stepTransitionDensity R.params R.coupling W b V := by
  classical
  unfold baseKernelLaw stepTransitionDensity baseLaw
  split_ifs
  · rfl
  · exact zero_mul _
private theorem stepWeight_eq_mul (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    stepWeight R C V W Yt ωt bad b =
      R.labelWeight (n * R.params.side) W Yt ωt * baseKernelLaw R V W b * markProduct R C V W bad := by
  unfold stepWeight baseKernelLaw
  ring
private theorem stepWeight_nonneg (hD : StepTransitionDensityBounds) (hR : R.IsWellPosed)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ωt bad b := by
  obtain ⟨Cd, hCd⟩ := (hD R.params R.coupling n).2
  rw [stepWeight_eq_mul, baseKernelLaw_eq]
  exact mul_nonneg (mul_nonneg (hR.hasExpansions.2.nonneg _ hside W Yt ωt hh) (hCd W b V).1)
    (markProduct_bounds hR C V W bad).1
end StepWeights
section LiveResponse
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
open Classical in
private def liveResponse (V : TorusField n) (Y : TorusSite n) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω) : ℝ :=
  if IsLiveState R.params R.coupling R.labelWeight W Yt ωt then
    caseResponse A V Y (constOneWeight _) W Yt ωt ∅ b else 0
private theorem measurable_blockBondScores (hS : BondScoreProperties) (hR : R.IsWellPosed) (V : TorusField n)
    (Y : TorusSite n) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) => blockBondScores (R := R) W V b Y := by
  have hk : Measurable fun W : TorusField (n * R.params.side) => (W, V) := measurable_prodMk_right
  have h : ∀ c : TorusBond n, Measurable fun W : TorusField (n * R.params.side) =>
      bondScore R.params R.coupling W V b c := by
    intro c
    obtain ⟨-, -, -, -, hm⟩ := hS R.params hR.admissible R.coupling n b c
    have h1 := hm.comp hk
    exact h1
  have e : (fun W : TorusField (n * R.params.side) => blockBondScores (R := R) W V b Y) = fun W =>
      ∑ i : Fin 4, (bondScore R.params R.coupling W V b (Y, i) +
        bondScore R.params R.coupling W V b (Y - TorusFields.unitStep n i, i)) := rfl
  rw [e]
  exact Finset.measurable_sum _ fun i _ => (h (Y, i)).add (h (Y - TorusFields.unitStep n i, i))
private theorem abs_blockBondScores_le (hS : BondScoreProperties) (hR : R.IsWellPosed)
    (W : TorusField (n * R.params.side)) (V : TorusField n)
    (Y : TorusSite n) (b : BaseChoice R.params.side n) : |blockBondScores (R := R) W V b Y| ≤ 16 := by
  have h : ∀ c : TorusBond n, |bondScore R.params R.coupling W V b c| ≤ 2 := fun c =>
    (hS R.params hR.admissible R.coupling n b c).2.2.1 W V
  unfold blockBondScores
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      |bondScore R.params R.coupling W V b (Y, i) + bondScore R.params R.coupling W V b (Y - TorusFields.unitStep n i, i)| ≤ 4 :=
    fun i _ => (abs_add_le _ _).trans (by linarith [h (Y, i), h (Y - TorusFields.unitStep n i, i)])
  refine (Finset.sum_le_sum this).trans ?_
  simp
  norm_num
private theorem measurableSet_isLiveState (hR : R.IsWellPosed) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have e : {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} =
      {p | 0 < (if IsHullState R.params (clusterRange R.coupling) p.1 Yt then
        R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0)} := by
    ext p
    by_cases h : IsHullState R.params (clusterRange R.coupling) p.1 Yt <;> simp [IsLiveState, h]
  rw [e]
  exact measurableSet_lt measurable_const (hR.hasExpansions.2.borel (n * R.params.side) hside Yt).1
private theorem measurable_liveResponse (hS : BondScoreProperties) (hR : R.IsWellPosed) (hA : A.IsAdmissible)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n) (Y : TorusSite n)
    (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => liveResponse A V Y Yt b p.1 p.2 := by
  classical
  have h1 : ∀ y, Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
        A.hull (n * R.params.side) y p.1 Yt p.2 (constOneWeight _) else 0 := fun y =>
    hA.bounds.hull_borel (n * R.params.side) hside y Yt _
  have h2 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then blockBondScores (R := R) p.1 V b Y else 0 :=
    Measurable.ite (measurableSet_isLiveState hR hside Yt)
      ((measurable_blockBondScores hS hR V Y b).comp measurable_fst) measurable_const
  have e : (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => liveResponse A V Y Yt b p.1 p.2) =
      fun p =>
      ∑ y ∈ sitesInBlocks R.params.side {Y},
          (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
            A.hull (n * R.params.side) y p.1 Yt p.2 (constOneWeight _) else 0) +
        R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y (constOneWeight _) *
          (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
            blockBondScores (R := R) p.1 V b Y else 0) := by
    funext p
    unfold liveResponse caseResponse
    by_cases h : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
    · simp only [if_pos h]
      rfl
    · simp only [if_neg h]
      simp
  rw [e]
  exact (Finset.measurable_sum _ fun y _ => h1 y).add (h2.const_mul _)
private theorem abs_liveResponse_le (hS : BondScoreProperties) (hR : R.IsWellPosed) (hA : A.IsAdmissible)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n) (Y : TorusSite n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
      (W : TorusField (n * R.params.side))
      (ωt : Yt → R.labels.Ω), |liveResponse A V Y Yt b W ωt| ≤ M * Real.exp (∑ y : Yt, A.score (ωt y)) := by
  classical
  set h₀ : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)) := constOneWeight _ with hh₀
  set sz : ℝ := |weightNorm R.params.side R.depth h₀| with hsz
  set c : ℝ := R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y (constOneWeight _) with hc
  set m : TorusSite (n * R.params.side) → ℝ := fun y =>
    |A.cold (n * R.params.side) y (trivialField _) h₀| + (|A.responseParams.C₀| + 1) * sz with hm
  have hm0 : ∀ y, 0 ≤ m y := fun y => add_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))
  refine ⟨∑ y ∈ sitesInBlocks R.params.side {Y}, m y + |c| * 16,
    add_nonneg (Finset.sum_nonneg fun y _ => hm0 y) (by positivity), fun Yt b W ωt => ?_⟩
  set S : ℝ := ∑ y : Yt, A.score (ωt y) with hSd
  have hs0 : ∀ w, 0 ≤ A.score w := hA.price.nonneg
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun y _ => hs0 _
  have hE1 : 1 ≤ Real.exp S := Real.one_le_exp hS0
  have hE2 : S ≤ Real.exp S := by linarith [Real.add_one_le_exp S]
  have hE0 : 0 < Real.exp S := Real.exp_pos S
  have htot : 0 ≤ (∑ y ∈ sitesInBlocks R.params.side {Y}, m y + |c| * 16) * Real.exp S :=
    mul_nonneg (add_nonneg (Finset.sum_nonneg fun y _ => hm0 y) (by positivity)) hE0.le
  unfold liveResponse
  split_ifs with hl
  swap
  · simpa using htot
  have hq : ∀ y, |A.hull (n * R.params.side) y W Yt ωt h₀| ≤ m y * Real.exp S := by
    intro y
    have h1 := hA.bounds.size_hull (n * R.params.side) hside y W Yt ωt hl h₀
    unfold centeredHullResponse at h1
    have hsc0 : 0 ≤ siteScore A.score Yt ωt y := by
      unfold siteScore
      split_ifs
      · exact hs0 _
      · exact le_rfl
    have hsc : siteScore A.score Yt ωt y ≤ Real.exp S := by
      unfold siteScore
      split_ifs with hy
      · refine le_trans ?_ hE2
        exact Finset.single_le_sum (f := fun y : Yt => A.score (ωt y)) (fun y _ => hs0 _)
          (Finset.mem_univ (⟨y, hy⟩ : Yt))
      · exact hE0.le
    have h2 : (A.responseParams.C₀ + siteScore A.score Yt ωt y) * weightNorm R.params.side R.depth h₀ ≤
        (|A.responseParams.C₀| + 1) * sz * Real.exp S := by
      have e1 : (A.responseParams.C₀ + siteScore A.score Yt ωt y) * weightNorm R.params.side R.depth h₀ ≤
          |A.responseParams.C₀ + siteScore A.score Yt ωt y| * sz := by
        rw [hsz, ← abs_mul]
        exact le_abs_self _
      have e2 : |A.responseParams.C₀ + siteScore A.score Yt ωt y| ≤ (|A.responseParams.C₀| + 1) * Real.exp S := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg hsc0, add_mul, one_mul]
        have : |A.responseParams.C₀| ≤ |A.responseParams.C₀| * Real.exp S :=
          le_mul_of_one_le_right (abs_nonneg _) hE1
        linarith
      calc _ ≤ _ := e1
        _ ≤ (|A.responseParams.C₀| + 1) * Real.exp S * sz := mul_le_mul_of_nonneg_right e2 (abs_nonneg _)
        _ = _ := by ring
    have h3 : |A.hull (n * R.params.side) y W Yt ωt h₀| ≤ |A.cold (n * R.params.side) y (trivialField _) h₀| +
        |A.hull (n * R.params.side) y W Yt ωt h₀ - A.cold (n * R.params.side) y (trivialField _) h₀| := by
      have := abs_add_le (A.cold (n * R.params.side) y (trivialField _) h₀)
        (A.hull (n * R.params.side) y W Yt ωt h₀ - A.cold (n * R.params.side) y (trivialField _) h₀)
      simpa using this
    have h4 : |A.cold (n * R.params.side) y (trivialField _) h₀| ≤
        |A.cold (n * R.params.side) y (trivialField _) h₀| * Real.exp S :=
      le_mul_of_one_le_right (abs_nonneg _) hE1
    simp only [hm, add_mul]
    linarith
  show |∑ y ∈ sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) y W Yt ωt h₀ +
    c * blockBondScores (R := R) W V b Y| ≤ _
  refine (abs_add_le _ _).trans ?_
  rw [add_mul, Finset.sum_mul]
  refine add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => hq y)) ?_
  rw [abs_mul]
  have h6 := abs_blockBondScores_le hS hR W V Y b
  calc |c| * |blockBondScores (R := R) W V b Y| ≤ |c| * 16 := mul_le_mul_of_nonneg_left h6 (abs_nonneg _)
    _ ≤ |c| * 16 * Real.exp S := le_mul_of_one_le_right (by positivity) hE1
private theorem lintegral_configurationWeight_mul_ne_top (hD : StepTransitionDensityBounds)
    (hM : ScoredMassStatement)
    (hR : R.IsWellPosed) (hA : A.IsAdmissible) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal) (M : ℝ)
    (hg : ∀ W ωt, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      g W ωt ≤ ENNReal.ofReal (M * Real.exp (∑ y : Yt, A.score (ωt y)))) :
    ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt * g W ωt
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) ≠ ⊤ := by
  classical
  obtain ⟨Cd, hCd⟩ := (hD R.params R.coupling n).2
  set Ms : ℝ := R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
    2 ^ Fintype.card (TorusSite (n * R.params.side)) *
    Real.exp (2 * R.params.E * Fintype.card (TorusSite (n * R.params.side))) with hMs
  have hmass := hM R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
    R.siteDensity A.score hR.admissible hR.admissible.E_ge hR.coupling_pos hR.range_ge_base
    hR.hasExpansions.1 hR.hasExpansions.2 hA.price (n * R.params.side) hside
  have hpt : ∀ W ωt, configurationWeight R C V bad Yt b W ωt * g W ωt ≤
      ENNReal.ofReal (Cd * M) * (if IsHullState R.params R.range W Yt then
        ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * Real.exp (∑ y : Yt, A.score (ωt y)))
        else 0) := by
    intro W ωt
    unfold configurationWeight
    by_cases hh : IsHullState R.params R.range W Yt
    · rw [if_pos hh, if_pos hh]
      have hD0 := hR.hasExpansions.2.nonneg _ hside W Yt ωt hh
      by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt
      · have hw : stepWeight R C V W Yt ωt bad b ≤ R.labelWeight (n * R.params.side) W Yt ωt * Cd := by
          rw [stepWeight_eq_mul, baseKernelLaw_eq, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hD0
          have h1 := hCd W b V
          have h2 := markProduct_bounds hR C V W bad
          calc _ ≤ stepTransitionDensity R.params R.coupling W b V * 1 := mul_le_mul_of_nonneg_left h2.2 h1.1
            _ ≤ Cd := by linarith [h1.2]
        have hCd0 : 0 ≤ Cd := (hCd W b V).1.trans (hCd W b V).2
        calc ENNReal.ofReal (stepWeight R C V W Yt ωt bad b) * g W ωt
            ≤ ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * Cd) *
                ENNReal.ofReal (M * Real.exp (∑ y : Yt, A.score (ωt y))) :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hw) (hg W ωt hl)
          _ = _ := by
              rw [← ENNReal.ofReal_mul (mul_nonneg hD0 hCd0), ← ENNReal.ofReal_mul' ?_]
              · congr 1
                ring
              · exact mul_nonneg hD0 (Real.exp_pos _).le
      · have hz : R.labelWeight (n * R.params.side) W Yt ωt = 0 :=
          le_antisymm (not_lt.mp fun h => hl ⟨hh, h⟩) hD0
        have : stepWeight R C V W Yt ωt bad b = 0 := by
          rw [stepWeight_eq_mul, hz]
          ring
        rw [this]
        simp
    · rw [if_neg hh, if_neg hh]
      simp
  have hin : ∀ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt * g W ωt
      ∂(Measure.pi fun _ => R.labels.μ) ≤
      ENNReal.ofReal (Cd * M) * ENNReal.ofReal Ms := by
    intro W
    refine (lintegral_mono (hpt W)).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_right ?_ _
    by_cases hh : IsHullState R.params R.range W Yt
    · simp only [if_pos hh]
      refine le_trans ?_ (hmass W)
      exact Finset.single_le_sum (f := fun Y : Finset (TorusSite (n * R.params.side)) =>
        ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω * Real.exp (∑ y : Y, A.score (ω y)))
          ∂(Measure.pi fun _ : Y => R.labels.μ)) (fun _ _ => zero_le)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    · simp [if_neg hh]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hin)
  simp [ENNReal.mul_eq_top]
end LiveResponse
section Configurations
variable {R : StepSetup} (A : ResponseSetup R) (n : ℕ) [NeZero n]
private structure Hypotheses : Prop where
  hS : BondScoreProperties
  hD : StepTransitionDensityBounds
  hM : ScoredMassStatement
  hF : ConfigurationMassWithFunction
  hw : ConfigurationWeightMeasurable
  hMean : BlockMeanIsLinearAndLocal
  hR : R.IsWellPosed
  hA : A.IsAdmissible
  hn : R.params.n₀ ≤ n
  hside : IsBlockTorusSide R.params (n * R.params.side)
variable {A n} (K : Hypotheses A n)
private def livePositivePart (A : ResponseSetup R) (V : TorusField n) (Y : TorusSite n)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal := fun W ωt =>
  ENNReal.ofReal (liveResponse A V Y Yt b W ωt)
private def liveNegativePart (A : ResponseSetup R) (V : TorusField n) (Y : TorusSite n)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal := fun W ωt =>
  ENNReal.ofReal (-liveResponse A V Y Yt b W ωt)
include K
private theorem measurable_livePositivePart (V : TorusField n) (Y : TorusSite n)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => livePositivePart A V Y Yt b p.1 p.2 :=
  (measurable_liveResponse A K.hS K.hR K.hA K.hside V Y Yt b).ennreal_ofReal
private theorem measurable_liveNegativePart (V : TorusField n) (Y : TorusSite n)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => liveNegativePart A V Y Yt b p.1 p.2 :=
  (measurable_liveResponse A K.hS K.hR K.hA K.hside V Y Yt b).neg.ennreal_ofReal
private theorem lintegral_parts_ne_top (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    (∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt * livePositivePart A V Y Yt b W ωt
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) ≠ ⊤) ∧
    (∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt * liveNegativePart A V Y Yt b W ωt
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) ≠ ⊤) ∧
    (∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt * 1
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) ≠ ⊤) := by
  obtain ⟨M, -, hM⟩ := abs_liveResponse_le A K.hS K.hR K.hA K.hside V Y
  refine ⟨lintegral_configurationWeight_mul_ne_top A K.hD K.hM K.hR K.hA K.hside C V bad Yt b _ M
      fun W ωt _ => ?_,
    lintegral_configurationWeight_mul_ne_top A K.hD K.hM K.hR K.hA K.hside C V bad Yt b _ M fun W ωt _ => ?_,
    lintegral_configurationWeight_mul_ne_top A K.hD K.hM K.hR K.hA K.hside C V bad Yt b (fun _ _ => 1) 1
      fun W ωt _ => ?_⟩
  · exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM Yt b W ωt))
  · exact ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hM Yt b W ωt))
  · have h0 : 0 ≤ ∑ y : Yt, A.score (ωt y) := Finset.sum_nonneg fun y _ => K.hA.price.nonneg _
    rw [one_mul, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp h0)
private theorem caseTerm_parts (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (q : CoarseState R n)
    (W : TorusField (n * R.params.side))
    (ν : q.unlabelled Yt → R.labels.Ω) :
    ENNReal.ofReal (caseTerm R C V q (caseResponse A V Y (constOneWeight _)) bad Yt b W ν) =
        stateMassTerm R C V bad Yt b (livePositivePart A V Y Yt b) q W ν ∧
      ENNReal.ofReal (-caseTerm R C V q (caseResponse A V Y (constOneWeight _)) bad Yt b W ν) =
        stateMassTerm R C V bad Yt b (liveNegativePart A V Y Yt b) q W ν := by
  classical
  unfold caseTerm stateMassTerm
  by_cases hc : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
  · rw [if_pos hc, if_pos hc, if_pos hc]
    set w := stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b with hw
    have hw0 : 0 ≤ w := stepWeight_nonneg K.hD K.hR K.hside C V _ Yt _ bad b hc.1
    have e : caseResponse A V Y (constOneWeight _) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b * w =
        liveResponse A V Y Yt b (q.fieldWithStoredLinks W) (q.fillLabels Yt ν) * w := by
      unfold liveResponse
      by_cases hl : IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν)
      · rw [if_pos hl]
        rfl
      · have hD0 := K.hR.hasExpansions.2.nonneg _ K.hside _ Yt (q.fillLabels Yt ν) hc.1
        have hz : R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) = 0 :=
          le_antisymm (not_lt.mp fun h => hl ⟨hc.1, h⟩) hD0
        have : w = 0 := by
          rw [hw, stepWeight_eq_mul, hz]
          ring
        rw [this, mul_zero, mul_zero]
    rw [e]
    constructor
    · rw [ENNReal.ofReal_mul' hw0, mul_comm]
      rfl
    · rw [← neg_mul, ENNReal.ofReal_mul' hw0, mul_comm]
      rfl
  · rw [if_neg hc, if_neg hc, if_neg hc]
    simp
private def stateIntegral (A : ResponseSetup R) (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (q : CoarseState R n) : ℝ :=
  ∫ W, ∫ ν : q.unlabelled Yt → R.labels.Ω, caseTerm R C V q (caseResponse A V Y (constOneWeight _)) bad Yt b W ν
    ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
private theorem stateIntegral_eq (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (q : CoarseState R n)
    (hp : configurationMassWith R C V bad Yt b (livePositivePart A V Y Yt b) q ≠ ⊤)
    (hm : configurationMassWith R C V bad Yt b (liveNegativePart A V Y Yt b) q ≠ ⊤) :
    stateIntegral A C V Y bad Yt b q = (configurationMassWith R C V bad Yt b (livePositivePart A V Y Yt b) q).toReal -
      (configurationMassWith R C V bad Yt b (liveNegativePart A V Y Yt b) q).toReal := by
  classical
  have hwb := K.hw R K.hR n K.hn C V bad Yt b
  have bP := measurable_stateMassTerm C V bad Yt b hwb _ (measurable_livePositivePart K V Y Yt b) q
  have bM := measurable_stateMassTerm C V bad Yt b hwb _ (measurable_liveNegativePart K V Y Yt b) q
  have hmeas : Measurable (Function.uncurry fun (W : TorusField (n * R.params.side))
      (ν : q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q (caseResponse A V Y (constOneWeight _)) bad Yt b W ν) := by
    have e : (Function.uncurry fun (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) =>
        caseTerm R C V q (caseResponse A V Y (constOneWeight _)) bad Yt b W ν) = fun p =>
        (Function.uncurry (stateMassTerm R C V bad Yt b (livePositivePart A V Y Yt b) q) p).toReal -
          (Function.uncurry (stateMassTerm R C V bad Yt b (liveNegativePart A V Y Yt b) q) p).toReal := by
      funext p
      obtain ⟨h1, h2⟩ := caseTerm_parts K C V Y bad Yt b q p.1 p.2
      simp only [Function.uncurry]
      rw [← h1, ← h2]
      exact eq_toReal_ofReal_sub_toReal_ofReal_neg _
    rw [e]
    exact bP.ennreal_toReal.sub bM.ennreal_toReal
  have eP : ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      ENNReal.ofReal (caseTerm R C V q (caseResponse A V Y (constOneWeight _)) bad Yt b W ν)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      configurationMassWith R C V bad Yt b (livePositivePart A V Y Yt b) q :=
    lintegral_congr fun W => lintegral_congr fun ν => (caseTerm_parts K C V Y bad Yt b q W ν).1
  have eM : ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      ENNReal.ofReal (-caseTerm R C V q (caseResponse A V Y (constOneWeight _)) bad Yt b W ν)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      configurationMassWith R C V bad Yt b (liveNegativePart A V Y Yt b) q :=
    lintegral_congr fun W => lintegral_congr fun ν => (caseTerm_parts K C V Y bad Yt b q W ν).2
  have h := (integrable_and_iterated_integral_eq (fieldHaar (n * R.params.side))
    (Measure.pi fun _ : (q.unlabelled Yt : Finset _) => R.labels.μ)
    (fun W ν => caseTerm R C V q (caseResponse A V Y (constOneWeight _)) bad Yt b W ν) hmeas
    (by rw [eP]; exact hp) (by rw [eM]; exact hm)).2
  rw [eP, eM] at h
  exact h
private def configurationIntegrand (A : ResponseSetup R) (C : Finset (TorusSite n)) (V : TorusField n)
    (Y : TorusSite n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω) : ℝ :=
  (configurationWeight R C V bad Yt b W ωt).toReal * liveResponse A V Y Yt b W ωt
private theorem configurationIntegrand_facts (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Integrable (Function.uncurry (configurationIntegrand A C V Y bad Yt b))
        ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) ∧
      ∫ W, ∫ ωt : Yt → R.labels.Ω, configurationIntegrand A C V Y bad Yt b W ωt
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
        (∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt * livePositivePart A V Y Yt b W ωt
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))).toReal -
        (∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt * liveNegativePart A V Y Yt b W ωt
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))).toReal := by
  classical
  have hwb := K.hw R K.hR n K.hn C V bad Yt b
  have hfin : ∀ W ωt, configurationWeight R C V bad Yt b W ωt ≠ ⊤ := by
    intro W ωt
    unfold configurationWeight
    split_ifs
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  have hmeas : Measurable (Function.uncurry (configurationIntegrand A C V Y bad Yt b)) :=
    hwb.ennreal_toReal.mul (measurable_liveResponse A K.hS K.hR K.hA K.hside V Y Yt b)
  have eP : ∀ W ωt, ENNReal.ofReal (configurationIntegrand A C V Y bad Yt b W ωt) =
      configurationWeight R C V bad Yt b W ωt * livePositivePart A V Y Yt b W ωt := by
    intro W ωt
    unfold configurationIntegrand livePositivePart
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin W ωt)]
  have eM : ∀ W ωt, ENNReal.ofReal (-configurationIntegrand A C V Y bad Yt b W ωt) =
      configurationWeight R C V bad Yt b W ωt * liveNegativePart A V Y Yt b W ωt := by
    intro W ωt
    unfold configurationIntegrand liveNegativePart
    rw [← mul_neg, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin W ωt)]
  simp_rw [← eP, ← eM]
  obtain ⟨f1, f2, -⟩ := lintegral_parts_ne_top K C V Y bad Yt b
  exact integrable_and_iterated_integral_eq _ _ _ hmeas (by simp_rw [eP]; exact f1) (by simp_rw [eM]; exact f2)
private theorem stateIntegral_integral (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (Y' : Finset (TorusSite n))
    (hY : Y' = coarseHull R.params.side R.range R.nextRange bad Yt C) :
    Integrable (fun ω : Y' → CoarseLabel R.labels.Ω R.params.side => stateIntegral A C V Y bad Yt b ⟨Y', ω⟩)
        (Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) ∧
      ∫ ω : Y' → CoarseLabel R.labels.Ω R.params.side, stateIntegral A C V Y bad Yt b ⟨Y', ω⟩
          ∂(Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) =
        ∫ W, ∫ ωt : Yt → R.labels.Ω, configurationIntegrand A C V Y bad Yt b W ωt
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  subst hY
  obtain ⟨-, -, mP, iP⟩ := K.hF R K.hR n K.hn C V bad Yt b _ (measurable_livePositivePart K V Y Yt b)
  obtain ⟨-, -, mM, iM⟩ := K.hF R K.hR n K.hn C V bad Yt b _ (measurable_liveNegativePart K V Y Yt b)
  obtain ⟨f1, f2, -⟩ := lintegral_parts_ne_top K C V Y bad Yt b
  rw [← iP] at f1
  rw [← iM] at f2
  have hae : (fun ω => stateIntegral A C V Y bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩)
      =ᵐ[Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side]
      fun ω => (configurationMassWith R C V bad Yt b (livePositivePart A V Y Yt b)
          ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩).toReal -
        (configurationMassWith R C V bad Yt b (liveNegativePart A V Y Yt b)
          ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩).toReal := by
    filter_upwards [ae_lt_top mP f1, ae_lt_top mM f2] with ω h1 h2
    exact stateIntegral_eq K C V Y bad Yt b _ h1.ne h2.ne
  have iP' := integrable_toReal_of_lintegral_ne_top mP.aemeasurable f1
  have iM' := integrable_toReal_of_lintegral_ne_top mM.aemeasurable f2
  refine ⟨(iP'.sub iM').congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub iP' iM', integral_toReal mP.aemeasurable (ae_lt_top mP f1),
    integral_toReal mM.aemeasurable (ae_lt_top mM f2), iP, iM, (configurationIntegrand_facts K C V Y bad Yt b).2]
private theorem stateIntegral_of_ne_coarseHull (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (q : CoarseState R n)
    (hq : q.1 ≠ coarseHull R.params.side R.range R.nextRange bad Yt C) : stateIntegral A C V Y bad Yt b q = 0 := by
  have h1 := (K.hF R K.hR n K.hn C V bad Yt b _ (measurable_livePositivePart K V Y Yt b)).1 q hq
  have h2 := (K.hF R K.hR n K.hn C V bad Yt b _ (measurable_liveNegativePart K V Y Yt b)).1 q hq
  rw [stateIntegral_eq K C V Y bad Yt b q (by rw [h1]; simp) (by rw [h2]; simp), h1, h2]
  simp
private theorem stateIntegral_of_configurationMass_eq_zero (C : Finset (TorusSite n)) (V : TorusField n)
    (Y : TorusSite n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (q : CoarseState R n)
    (hq : configurationMass R C V bad Yt b q = 0) : stateIntegral A C V Y bad Yt b q = 0 := by
  have h1 := (K.hF R K.hR n K.hn C V bad Yt b _ (measurable_livePositivePart K V Y Yt b)).2.1 q hq
  have h2 := (K.hF R K.hR n K.hn C V bad Yt b _ (measurable_liveNegativePart K V Y Yt b)).2.1 q hq
  rw [stateIntegral_eq K C V Y bad Yt b q (by rw [h1]; simp) (by rw [h2]; simp), h1, h2]
  simp
private theorem caseIntegral_eq_sum (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (q : CoarseState R n) :
    caseIntegral R C V q (caseResponse A V Y (constOneWeight _)) =
      ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n, stateIntegral A C V Y bad Yt b q := rfl
private theorem caseMean_mul_ae (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (Y' : Finset (TorusSite n)) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Y' => coarseLabelMeasure R.labels.μ R.params.side),
      caseMean R C V ⟨Y', ω⟩ (caseResponse A V Y (constOneWeight _)) * coarseStateWeight R C V ⟨Y', ω⟩ =
        caseIntegral R C V ⟨Y', ω⟩ (caseResponse A V Y (constOneWeight _)) := by
  classical
  have hone : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) (q : CoarseState R n),
      configurationMassWith R C V bad Yt b (fun _ _ => 1) q = configurationMass R C V bad Yt b q := by
    intro bad Yt b q
    simp only [configurationMassWith, configurationMass, mul_one]
  have hfin : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      ∀ᵐ ω ∂(Measure.pi fun _ : Y' => coarseLabelMeasure R.labels.μ R.params.side),
        configurationMass R C V bad Yt b ⟨Y', ω⟩ ≠ ⊤ := by
    intro bad Yt b
    by_cases hY : Y' = coarseHull R.params.side R.range R.nextRange bad Yt C
    · subst hY
      obtain ⟨-, -, m1, i1⟩ := K.hF R K.hR n K.hn C V bad Yt b (fun _ _ => 1) measurable_const
      obtain ⟨-, -, f3⟩ := lintegral_parts_ne_top K C V Y bad Yt b
      rw [← i1] at f3
      filter_upwards [ae_lt_top m1 f3] with ω h
      rw [← hone]
      exact h.ne
    · refine Filter.Eventually.of_forall fun ω => ?_
      have := (K.hF R K.hR n K.hn C V bad Yt b (fun _ _ => 1) measurable_const).1 ⟨Y', ω⟩ hY
      rw [hone] at this
      rw [this]
      simp
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : Y' => coarseLabelMeasure R.labels.μ R.params.side),
      ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
        (b : BaseChoice R.params.side n),
        configurationMass R C V bad Yt b ⟨Y', ω⟩ ≠ ⊤ := by
    rw [ae_all_iff]
    intro bad
    rw [ae_all_iff]
    intro Yt
    rw [ae_all_iff]
    intro b
    exact hfin bad Yt b
  filter_upwards [hall] with ω hω
  have hmass : coarseStateMass R C V ⟨Y', ω⟩ = ∑ bad ∈ (markedBonds R C).powerset,
      ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n, configurationMass R C V bad Yt b ⟨Y', ω⟩ := rfl
  have hne : coarseStateMass R C V ⟨Y', ω⟩ ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.sum_ne_top.mpr fun bad _ => ENNReal.sum_ne_top.mpr fun Yt _ =>
      ENNReal.sum_ne_top.mpr fun b _ => hω bad Yt b
  unfold caseMean
  by_cases hz : coarseStateWeight R C V ⟨Y', ω⟩ = 0
  · rw [hz, mul_zero]
    have h0 : coarseStateMass R C V ⟨Y', ω⟩ = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hz with h | h
      · exact h
      · exact absurd h hne
    rw [hmass] at h0
    rw [caseIntegral_eq_sum K]
    refine (Finset.sum_eq_zero fun bad hbad => Finset.sum_eq_zero fun Yt _ =>
      Finset.sum_eq_zero fun b _ => ?_).symm
    refine stateIntegral_of_configurationMass_eq_zero K C V Y bad Yt b _ ?_
    have h1 := Finset.sum_eq_zero_iff.mp h0 bad hbad
    have h2 := Finset.sum_eq_zero_iff.mp h1 Yt (Finset.mem_univ _)
    exact Finset.sum_eq_zero_iff.mp h2 b (Finset.mem_univ _)
  · exact div_mul_cancel₀ _ hz
open Classical in
private def markFreeIntegrand (A : ResponseSetup R) (V : TorusField n) (Y : TorusSite n)
    (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω) : ℝ :=
  if IsHullState R.params R.range W Yt then
    R.labelWeight (n * R.params.side) W Yt ωt * baseKernelLaw R V W b * liveResponse A V Y Yt b W ωt else 0
private theorem sum_over_marks (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    Integrable (Function.uncurry (markFreeIntegrand A V Y Yt b))
        ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) ∧
      ∑ bad ∈ (markedBonds R C).powerset,
        ∫ W, ∫ ωt : Yt → R.labels.Ω, configurationIntegrand A C V Y bad Yt b W ωt
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫ W, ∫ ωt : Yt → R.labels.Ω, markFreeIntegrand A V Y Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  have hi : ∀ bad ∈ (markedBonds R C).powerset, Integrable (Function.uncurry (configurationIntegrand A C V Y bad Yt b))
      ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := fun bad _ =>
    (configurationIntegrand_facts K C V Y bad Yt b).1
  have hpt : Function.uncurry (markFreeIntegrand A V Y Yt b) =
      fun p => ∑ bad ∈ (markedBonds R C).powerset, Function.uncurry (configurationIntegrand A C V Y bad Yt b) p := by
    funext p
    obtain ⟨W, ωt⟩ := p
    simp only [Function.uncurry, markFreeIntegrand, configurationIntegrand, configurationWeight]
    by_cases hh : IsHullState R.params R.range W Yt
    · simp only [if_pos hh]
      have e : ∀ bad, (ENNReal.ofReal (stepWeight R C V W Yt ωt bad b)).toReal * liveResponse A V Y Yt b W ωt =
          R.labelWeight (n * R.params.side) W Yt ωt * baseKernelLaw R V W b * liveResponse A V Y Yt b W ωt *
            markProduct R C V W bad := by
        intro bad
        rw [ENNReal.toReal_ofReal (stepWeight_nonneg K.hD K.hR K.hside C V W Yt ωt bad b hh), stepWeight_eq_mul]
        ring
      simp_rw [e]
      rw [← Finset.mul_sum, sum_markProduct, mul_one]
    · simp [if_neg hh]
  have hI : Integrable (Function.uncurry (markFreeIntegrand A V Y Yt b))
      ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := by
    rw [hpt]
    exact integrable_finsetSum _ hi
  refine ⟨hI, ?_⟩
  have e1 : ∀ bad ∈ (markedBonds R C).powerset,
      ∫ W, ∫ ωt : Yt → R.labels.Ω, configurationIntegrand A C V Y bad Yt b W ωt
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
        ∫ p, Function.uncurry (configurationIntegrand A C V Y bad Yt b) p
          ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) :=
    fun bad hbad => (integral_prod _ (hi bad hbad)).symm
  rw [Finset.sum_congr rfl e1, ← integral_finsetSum _ hi, ← hpt]
  exact integral_prod _ hI
end Configurations
section AtAField
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n] (K : Hypotheses A n)
include K
private theorem labelWeight_facts (W : TorusField (n * R.params.side)) :
    (open Classical in ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
        ∫ ωt : Yt → R.labels.Ω, R.labelWeight (n * R.params.side) W Yt ωt ∂(Measure.pi fun _ : Yt => R.labels.μ)) =
        R.functional (n * R.params.side) W ∧
      ∀ Yt : Finset (TorusSite (n * R.params.side)), IsHullState R.params (clusterRange R.coupling) W Yt →
        Integrable (fun ωt : Yt → R.labels.Ω => R.labelWeight (n * R.params.side) W Yt ωt)
          (Measure.pi fun _ : Yt => R.labels.μ) := by
  classical
  have hnL : R.params.n₀ ≤ n * R.params.side :=
    K.hn.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne R.params.side)))
  have hsum := K.hR.hasExpansions.2.sum (n * R.params.side) K.hside W
  have hD0 : 0 ≤ R.functional (n * R.params.side) W := (K.hR.functional_spec (n * R.params.side) hnL).2.1 W
  have hfin : ∀ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) ≠ ⊤ := by
    intro Yt hY h
    have h1 := Finset.single_le_sum (f := fun Y : Finset (TorusSite (n * R.params.side)) =>
      ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω) ∂(Measure.pi fun _ : Y => R.labels.μ))
      (fun _ _ => zero_le) hY
    rw [hsum] at h1
    simp only [h, top_le_iff] at h1
    exact ENNReal.ofReal_ne_top h1
  have hmeas : ∀ Yt : Finset (TorusSite (n * R.params.side)), IsHullState R.params (clusterRange R.coupling) W Yt →
      Measurable fun ω : Yt → R.labels.Ω => R.labelWeight (n * R.params.side) W Yt ω := by
    intro Yt hY
    have h1 := (K.hR.hasExpansions.2.borel (n * R.params.side) K.hside Yt).1.comp (measurable_prodMk_left (x := W))
    have e : ((fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsHullState R.params (clusterRange R.coupling) p.1 Yt then
          R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0) ∘ Prod.mk W) =
        fun ω => R.labelWeight (n * R.params.side) W Yt ω := by
      funext ω
      simp [hY]
    rwa [e] at h1
  have hnn : ∀ Yt : Finset (TorusSite (n * R.params.side)), IsHullState R.params (clusterRange R.coupling) W Yt →
      0 ≤ᵐ[Measure.pi fun _ : Yt => R.labels.μ] fun ω => R.labelWeight (n * R.params.side) W Yt ω := fun Yt hY =>
    Filter.Eventually.of_forall fun ω => K.hR.hasExpansions.2.nonneg _ K.hside W Yt ω hY
  refine ⟨?_, fun Yt hY => ?_⟩
  · have h2 : ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
        ∫ ωt : Yt → R.labels.Ω, R.labelWeight (n * R.params.side) W Yt ωt ∂(Measure.pi fun _ : Yt => R.labels.μ) =
        (∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
          ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ω)
            ∂(Measure.pi fun _ : Yt => R.labels.μ)).toReal := by
      rw [ENNReal.toReal_sum hfin]
      refine Finset.sum_congr rfl fun Yt hY => ?_
      exact integral_eq_lintegral_of_nonneg_ae (hnn Yt (Finset.mem_filter.mp hY).2)
        (hmeas Yt (Finset.mem_filter.mp hY).2).aestronglyMeasurable
    rw [h2, hsum, ENNReal.toReal_ofReal hD0]
  · refine ⟨(hmeas Yt hY).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (hnn Yt hY)]
    exact lt_top_iff_ne_top.mpr (hfin Yt (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hY⟩))
private theorem sum_integral_markFreeIntegrand (V : TorusField n) (Y : TorusSite n)
    (W : TorusField (n * R.params.side)) :
    ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
      ∫ ωt : Yt → R.labels.Ω, markFreeIntegrand A V Y Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ) =
        fieldBlockResponse A V Y W := by
  classical
  obtain ⟨hDs, hDi⟩ := labelWeight_facts K W
  have hhat : blockMean R.params.side (R.depth + 1) n Y (constOneWeight _) = 1 :=
    (K.hMean R.params.side K.hR.admissible.L_odd (R.depth + 1) n Y).1
  have hQi : ∀ (y : TorusSite (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))),
      IsHullState R.params (clusterRange R.coupling) W Yt →
      Integrable (fun ω : Yt → R.labels.Ω =>
        A.hull (n * R.params.side) y W Yt ω (constOneWeight _) * R.labelWeight (n * R.params.side) W Yt ω)
        (Measure.pi fun _ : Yt => R.labels.μ) := fun y Yt hY =>
    K.hA.bounds.mass_integrable (n * R.params.side) K.hside y W Yt hY
  have hone : ∀ (b : BaseChoice R.params.side n) (Yt : Finset (TorusSite (n * R.params.side))),
      ∫ ωt : Yt → R.labels.Ω, markFreeIntegrand A V Y Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ) =
        if IsHullState R.params (clusterRange R.coupling) W Yt then baseKernelLaw R V W b *
          (∑ y ∈ sitesInBlocks R.params.side {Y}, ∫ ωt : Yt → R.labels.Ω,
              A.hull (n * R.params.side) y W Yt ωt (constOneWeight _) *
              R.labelWeight (n * R.params.side) W Yt ωt ∂(Measure.pi fun _ : Yt => R.labels.μ) +
            R.params.coupling / 2 * A.coeff * blockBondScores (R := R) W V b Y *
              ∫ ωt : Yt → R.labels.Ω, R.labelWeight (n * R.params.side) W Yt ωt
                ∂(Measure.pi fun _ : Yt => R.labels.μ)) else 0 := by
    intro b Yt
    by_cases hh : IsHullState R.params (clusterRange R.coupling) W Yt
    · rw [if_pos hh]
      have hpt : ∀ ωt : Yt → R.labels.Ω, markFreeIntegrand A V Y Yt b W ωt = baseKernelLaw R V W b *
          (∑ y ∈ sitesInBlocks R.params.side {Y},
              A.hull (n * R.params.side) y W Yt ωt (constOneWeight _) * R.labelWeight (n * R.params.side) W Yt ωt +
            R.params.coupling / 2 * A.coeff * blockBondScores (R := R) W V b Y *
              R.labelWeight (n * R.params.side) W Yt ωt) := by
        intro ωt
        have hh' : IsHullState R.params R.range W Yt := hh
        unfold markFreeIntegrand liveResponse
        rw [if_pos hh']
        by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt
        · rw [if_pos hl]
          show R.labelWeight (n * R.params.side) W Yt ωt * baseKernelLaw R V W b *
            (∑ y ∈ sitesInBlocks R.params.side {Y},
              A.hull (n * R.params.side) y W Yt ωt (constOneWeight _) + R.params.coupling / 2 * A.coeff *
                blockMean R.params.side (R.depth + 1) n Y (constOneWeight _) *
              blockBondScores (R := R) W V b Y) = _
          rw [hhat, ← Finset.sum_mul]
          ring
        · have hz : R.labelWeight (n * R.params.side) W Yt ωt = 0 :=
            le_antisymm (not_lt.mp fun h => hl ⟨hh, h⟩) (K.hR.hasExpansions.2.nonneg _ K.hside W Yt ωt hh')
          simp [hz]
      simp_rw [hpt]
      rw [integral_const_mul, integral_add (integrable_finsetSum _ fun y _ => hQi y Yt hh)
        ((hDi Yt hh).const_mul _), integral_finsetSum _ fun y _ => hQi y Yt hh, integral_const_mul]
    · have hh' : ¬ IsHullState R.params R.range W Yt := hh
      rw [if_neg hh]
      have : ∀ ωt : Yt → R.labels.Ω, markFreeIntegrand A V Y Yt b W ωt = 0 := fun ωt => if_neg hh'
      simp_rw [this]
      simp
  rw [Finset.sum_comm]
  unfold fieldBlockResponse
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [hone b]
  rw [← Finset.sum_filter, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum, hDs]
  rfl
private theorem sum_integral_configurationIntegrand (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n) :
    ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n,
      ∫ W, ∫ ωt : Yt → R.labels.Ω, configurationIntegrand A C V Y bad Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
    blockResponseIntegral A V Y := by
  classical
  rw [Finset.sum_comm]
  have e1 : ∀ Yt : Finset (TorusSite (n * R.params.side)), ∑ bad ∈ (markedBonds R C).powerset,
      ∑ b : BaseChoice R.params.side n,
      ∫ W, ∫ ωt : Yt → R.labels.Ω, configurationIntegrand A C V Y bad Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∑ b : BaseChoice R.params.side n,
        ∫ W, ∫ ωt : Yt → R.labels.Ω, markFreeIntegrand A V Y Yt b W ωt
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
    intro Yt
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => (sum_over_marks K C V Y Yt b).2
  simp_rw [e1]
  have hi : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Integrable (fun W => ∫ ωt : Yt → R.labels.Ω, markFreeIntegrand A V Y Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ))
        (fieldHaar (n * R.params.side)) := fun Yt b => (sum_over_marks K C V Y Yt b).1.integral_prod_left
  have e2 : ∀ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
      ∫ W, ∫ ωt : Yt → R.labels.Ω, markFreeIntegrand A V Y Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫ W, ∑ b : BaseChoice R.params.side n, ∫ ωt : Yt → R.labels.Ω, markFreeIntegrand A V Y Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) := fun Yt => (integral_finsetSum _ fun b _ => hi Yt b).symm
  simp_rw [e2]
  rw [← integral_finsetSum _ fun Yt _ => integrable_finsetSum _ fun b _ => hi Yt b]
  unfold blockResponseIntegral
  exact integral_congr_ae (Filter.Eventually.of_forall fun W => sum_integral_markFreeIntegrand K V Y W)
end AtAField
section MainResult
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem coarseHull_empty (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) :
    coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coarseHull_empty <;> assumption
private theorem coarseWeightExpansion_eq (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    coarseWeightExpansion R n V Y ω = coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ := by
  simp only [coarseWeightExpansion, NeZero.ne n, dite_false]
private theorem integrable_stateIntegrals {A : ResponseSetup R} (K : Hypotheses A n) (C : Finset (TorusSite n))
    (V : TorusField n) (y : TorusSite n)
    (Y : Finset (TorusSite n)) :
    Integrable (fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
        caseIntegral R C V ⟨Y, ω⟩ (caseResponse A V y (constOneWeight _)))
      (Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) ∧
    ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Integrable (fun ω : Y → CoarseLabel R.labels.Ω R.params.side => stateIntegral A C V y bad Yt b ⟨Y, ω⟩)
        (Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) := by
  classical
  have h : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Integrable (fun ω : Y → CoarseLabel R.labels.Ω R.params.side => stateIntegral A C V y bad Yt b ⟨Y, ω⟩)
        (Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) := by
    intro bad Yt b
    by_cases hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt C
    · exact (stateIntegral_integral K C V y bad Yt b Y hY).1
    · have : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side => stateIntegral A C V y bad Yt b ⟨Y, ω⟩) =
          fun _ => 0 :=
        funext fun ω => stateIntegral_of_ne_coarseHull K C V y bad Yt b ⟨Y, ω⟩ hY
      rw [this]
      exact integrable_zero _ _ _
  refine ⟨?_, h⟩
  simp_rw [caseIntegral_eq_sum K]
  exact integrable_finsetSum _ fun bad _ => integrable_finsetSum _ fun Yt _ =>
    integrable_finsetSum _ fun b _ => h bad Yt b
theorem responseEqCaseIntegral (hS : BondScoreProperties) (hD : StepTransitionDensityBounds)
    (hM : ScoredMassStatement)
    (hF : ConfigurationMassWithFunction) (hw : ConfigurationWeightMeasurable)
    (hMean : BlockMeanIsLinearAndLocal) (hH : CoarseHullIsHullState) : responseEqCaseIntegralStatement := by
  classical
  intro R A hL hR hA
  have mk : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → Hypotheses A n := fun n _ hn =>
    ⟨hS, hD, hM, hF, hw, hMean, hR, hA, hn, Nat.dvd_mul_left _ _, by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ hn⟩
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne R.params.side)
  have hn₀ : ∀ n : ℕ, IsBlockTorusSide R.params n → R.params.n₀ ≤ n := fun n hn =>
    (Nat.le_mul_of_pos_left _ (by omega)).trans hn.2
  refine ⟨fun n _ hn y V Y hY => ?_, fun n _ hn y V => ?_, fun n _ hn y V => ?_⟩
  · have K := mk n (hn₀ n hn)
    refine (integrable_stateIntegrals K (hotCoreSites R V) V y Y).1.congr ?_
    filter_upwards [caseMean_mul_ae K (hotCoreSites R V) V y Y] with ω h
    rw [← h]
    show _ = caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ (caseResponse A V y (constOneWeight _)) *
      coarseWeightExpansion R n V Y ω
    rw [coarseWeightExpansion_eq]
  · have K := mk n (hn₀ n hn)
    set C := hotCoreSites R V with hC
    have hint : ∀ Y : Finset (TorusSite n),
        ∫ ω : Y → (coarseLabelSpace R hL).Ω, A.hullStep n y V Y ω (constOneWeight _) * coarseWeightExpansion R n V Y ω
          ∂(Measure.pi fun _ : Y => (coarseLabelSpace R hL).μ) =
        ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
          ∑ b : BaseChoice R.params.side n,
          ∫ ω : Y → CoarseLabel R.labels.Ω R.params.side, stateIntegral A C V y bad Yt b ⟨Y, ω⟩
            ∂(Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) := by
      intro Y
      have hi := (integrable_stateIntegrals K C V y Y).2
      have e : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
          A.hullStep n y V Y ω (constOneWeight _) * coarseWeightExpansion R n V Y ω)
          =ᵐ[Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side]
          fun ω => ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
            ∑ b : BaseChoice R.params.side n,
            stateIntegral A C V y bad Yt b ⟨Y, ω⟩ := by
        filter_upwards [caseMean_mul_ae K C V y Y] with ω h
        rw [← caseIntegral_eq_sum K, ← h, coarseWeightExpansion_eq]
        rfl
      refine (integral_congr_ae e).trans ?_
      rw [integral_finsetSum _ fun bad _ => integrable_finsetSum _ fun Yt _ =>
        integrable_finsetSum _ fun b _ => hi bad Yt b]
      refine Finset.sum_congr rfl fun bad _ => ?_
      rw [integral_finsetSum _ fun Yt _ => integrable_finsetSum _ fun b _ => hi bad Yt b]
      refine Finset.sum_congr rfl fun Yt _ => ?_
      exact integral_finsetSum _ fun b _ => hi bad Yt b
    unfold responseMass
    simp_rw [hint]
    rw [Finset.sum_comm, ← sum_integral_configurationIntegrand K C V y]
    refine Finset.sum_congr rfl fun bad _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hm : coarseHull R.params.side R.range R.nextRange bad Yt C ∈
        Finset.univ.filter (IsHullState R.params (clusterRange R.nextCoupling) V) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH R.params hR.admissible R.range R.nextRange hR.range_le
        hR.nextRange_ge n hn.1 V bad Yt⟩
    rw [Finset.sum_eq_single_of_mem _ hm]
    · exact (stateIntegral_integral K C V y bad Yt b _ rfl).2
    · intro Y _ hne
      have : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side => stateIntegral A C V y bad Yt b ⟨Y, ω⟩) =
          fun _ => 0 :=
        funext fun ω => stateIntegral_of_ne_coarseHull K C V y bad Yt b ⟨Y, ω⟩ hne
      simp_rw [this]
      simp
  · have K := mk n hn
    rw [caseIntegral_eq_sum K, ← sum_integral_configurationIntegrand K ∅ V y]
    refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ =>
      Finset.sum_congr rfl fun b _ => ?_
    rw [← (stateIntegral_integral K ∅ V y bad Yt b ∅ (coarseHull_empty bad Yt).symm).2]
    have hfun : (fun ω : (∅ : Finset (TorusSite n)) → CoarseLabel R.labels.Ω R.params.side =>
        stateIntegral A ∅ V y bad Yt b ⟨∅, ω⟩) =
        fun _ => stateIntegral A ∅ V y bad Yt b (emptyCoarseState R) := by
      funext ω
      have : (⟨∅, ω⟩ : CoarseState R n) = emptyCoarseState R :=
        congrArg (Sigma.mk _) (funext fun z => absurd z.2 (Finset.notMem_empty _))
      rw [this]
    have : IsEmpty (∅ : Finset (TorusSite n)) := ⟨fun z => Finset.notMem_empty _ z.2⟩
    let ω₀ : (∅ : Finset (TorusSite n)) → CoarseLabel R.labels.Ω R.params.side :=
      fun z => absurd z.2 (Finset.notMem_empty _)
    rw [hfun, Measure.pi_of_empty _ ω₀, integral_const]
    simp
end MainResult
end YangMills.Construction.WeightedResponses
end
