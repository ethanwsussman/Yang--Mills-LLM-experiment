import YangMills.Construction.ResponseInTheExpansion.GasResponseReadsItsSiteProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocksProof
import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeightProofForm
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGasAtAStep
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGasProof
import YangMills.Construction.FreeEnergiesOfTheFlow.FunctionsOfTheLabelsAreIntegrableProof
import YangMills.Construction.ResponseInTheExpansion.CaseMeanIsAMeanOfTheGasProof
import YangMills.Construction.ResponseInTheExpansion.ImageResponseIsAMeanOfTheGasProof
import YangMills.Construction.ResponseInTheExpansion.PartsOfTheGasAreColdMeans
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings StepGas TorusLumps TorusFields WeightedResponses RenormalizationStepParameters BlockAverages LumpContours
  ColdStepAtMirrorFrames Dobrushin TorusContours TopLevelSites StepCosts MarkedIntegrals ClusterExpansionOfAStep ClusterBounds
namespace ColdShiftLemmas
section Cutoffs
private theorem cutoff_le_one {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hc : IsCutoff ρ p) {t : ℝ} (h0 : 0 ≤ t) :
    cutoffFactor ρ p t ≤ 1 := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_le_one <;> assumption
private theorem cutoff_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
private theorem sum_powerset_marks {B : Type} [DecidableEq B] (M : Finset B) (m : B → ℝ) :
    ∑ bad ∈ M.powerset, ∏ b ∈ M, (if b ∈ bad then 1 - m b else m b) = 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.sum_powerset_prod_complement_eq_one <;> assumption
private theorem lintegral_relabel {S Ω : Type} [DecidableEq S] [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    {Y Y' : Finset S} (e : Y' = Y) (lab : (Y' → Ω) → (Y → Ω)) (h : ∀ ν z, lab ν z = ν ⟨z.1, e ▸ z.2⟩)
    (f : (Y → Ω) → ℝ≥0∞) :
    ∫⁻ ν, f (lab ν) ∂Measure.pi (fun _ : Y' => μ) = ∫⁻ ω, f ω ∂Measure.pi (fun _ : Y => μ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.lintegral_pi_reindex <;> assumption
end Cutoffs
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Empty
variable (R)
private theorem fieldWithStoredLinks_empty (W : TorusField (n * R.params.side)) :
    (emptyCoarseState R (n := n)).fieldWithStoredLinks W = W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.fieldWithStoredLinks_empty <;> assumption
private theorem labelAt_empty (z : TorusSite (n * R.params.side)) :
    (emptyCoarseState R (n := n)).labelAt z = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TrivialFieldGround.labelAt_empty <;> assumption
private theorem unlabelled_empty (Yt : Finset (TorusSite (n * R.params.side))) :
    (emptyCoarseState R (n := n)).unlabelled Yt = Yt := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.unlabelled_empty <;> assumption
private theorem fillLabels_empty {Yt : Finset (TorusSite (n * R.params.side))}
    (ν : (emptyCoarseState R (n := n)).unlabelled Yt → R.labels.Ω) (z : Yt) :
    (emptyCoarseState R (n := n)).fillLabels Yt ν z = ν ⟨z.1, (unlabelled_empty R Yt).symm ▸ z.2⟩ := by
  unfold CoarseState.fillLabels
  split
  · rename_i a heq
    rw [labelAt_empty] at heq
    cases heq
  · rfl
private theorem coarseStateOf_empty (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    coarseStateOf R (∅ : Finset (TorusSite n)) W Yt ωt bad b = emptyCoarseState R := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.coarseStateOf_empty <;> assumption
private theorem recordedBad_cold (V : TorusField n) : (coldCaseGround R V).recordedBad = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.recordedBad_coldCase <;> assumption
private theorem recordedSites_cold (V : TorusField n) : (coldCaseGround R V).recordedSites = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.recordedSites_coldCase <;> assumption
private theorem baseLaw_nonneg (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    0 ≤ baseLaw (R := R) W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SmoothOffHull.baseLaw_nonneg_of_field <;> assumption
private theorem averagedKernel_eq (W : TorusField (n * R.params.side)) (V : TorusField n) :
    averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) =
      ∑ b : BaseChoice R.params.side n, baseLaw (R := R) W b *
        ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
            (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.averagedKernel_eq_sum <;> assumption
private theorem markedBonds_empty : markedBonds R (∅ : Finset (TorusSite n)) = chartBonds R.params.side n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.markedBonds_empty <;> assumption
end Empty
section Gauges
private theorem isHullState_gaugeTransform (hfit : R.params.Admissible)
    (g : TorusSite (n * R.params.side) → UnitQuaternion) (W : TorusField (n * R.params.side)) (r : ℕ)
    (Y : Finset (TorusSite (n * R.params.side))) :
    IsHullState R.params r (TorusFields.gaugeTransform g W) Y ↔ IsHullState R.params r W Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.isHullState_gaugeTransform_iff <;> assumption
private theorem bondScore_gaugeTransform {g : TorusSite (n * R.params.side) → UnitQuaternion}
    (W : TorusField (n * R.params.side)) (V : TorusField n) {b : BaseChoice R.params.side n}
    (hb : ∀ e, g (toTorusSite (n * R.params.side) (b e)) = 1) (c : TorusBond n) :
    bondScore R.params R.coupling (TorusFields.gaugeTransform g W) V b c = bondScore R.params R.coupling W V b c := by apply _root_.YangMills.SharedProofs.p31057 <;> assumption
end Gauges
section Cases
private structure IsCaseReal (H : CaseFunction R n) : Prop where
  borel : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n),
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => H p.1 Yt p.2 bad b
  gauge : IsGaugeInvariantCase H
private def weightBy (f : ℝ → ℝ≥0∞) (H : CaseFunction R n) : CaseFunctional R n :=
  fun W Yt ωt bad b => f (H W Yt ωt bad b)
private theorem isCaseFunctional_weightBy {H : CaseFunction R n} (hH : IsCaseReal H) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) : IsCaseFunctional (weightBy f H) :=
  ⟨fun Yt bad b => hf.comp (hH.borel Yt bad b), fun W Yt ωt bad b u hh hp h1 h2 =>
    congrArg f (hH.gauge W Yt ωt bad b u ⟨hh, hp⟩ h1 h2)⟩
private theorem measurable_posPart : Measurable fun u : ℝ => ENNReal.ofReal u := ENNReal.measurable_ofReal
private theorem measurable_negPart : Measurable fun u : ℝ => ENNReal.ofReal (-u) :=
  ENNReal.measurable_ofReal.comp measurable_neg
private theorem measurable_absPart : Measurable fun u : ℝ => ENNReal.ofReal |u| :=
  ENNReal.measurable_ofReal.comp continuous_abs.measurable
private abbrev ColdFunction (R : StepSetup) (n : ℕ) [NeZero n] : Type :=
  (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
    TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ
private def lift (f : ColdFunction R n) : CaseFunction R n := fun W Yt ωt _ b => f Yt b (W, ωt)
private def coldWeight (R : StepSetup) {n : ℕ} [NeZero n] (V : TorusField n)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  hullBaseDensity R Yt b p * kernelProduct R.params R.coupling p.1 V b
private def coldMass (R : StepSetup) {n : ℕ} [NeZero n] (V : TorusField n)
    (φ : (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
      TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
    ∫⁻ p, φ Yt b p * ENNReal.ofReal (coldWeight R V Yt b p) ∂fieldLabelMeasure R n Yt
end Cases
section ColdCases
private structure Base (R : StepSetup) : Prop where
  fits : R.params.Admissible
  cut : IsCutoff R.ballRadius R.barrierFn
  row : R.HasExpansions
  kernel : BondKernelProperties
private theorem bondMark_bounds (hR : Base R) (V : TorusField n) (W : TorusField (n * R.params.side))
    (b : TorusBond (n * R.params.side)) : 0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 :=
  ⟨cutoff_nonneg _ _ _, cutoff_le_one (by have := hR.fits.σ_pos; unfold StepSetup.ballRadius; positivity) hR.cut
    (norm_nonneg _)⟩
private theorem markProduct_nonneg (hR : Base R) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side))) :
    0 ≤ markProduct R C V W bad := by
  classical
  unfold markProduct
  refine Finset.prod_nonneg fun b _ => ?_
  have := bondMark_bounds hR V W b
  split_ifs
  · linarith [this.2]
  · exact this.1
private theorem kernelProduct_nonneg (hR : Base R) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : BaseChoice R.params.side n) : 0 ≤ kernelProduct R.params R.coupling W V b :=
  Finset.prod_nonneg fun c _ => (hR.kernel.2 R.params R.coupling n _ _ b c).1.le
private theorem sum_markProduct (V : TorusField n) (W : TorusField (n * R.params.side)) :
    ∑ bad ∈ (markedBonds R (∅ : Finset (TorusSite n))).powerset, markProduct R ∅ V W bad = 1 := by
  classical
  have h := sum_powerset_marks (markedBonds R (∅ : Finset (TorusSite n))) (fun b => bondMark R V W b)
  unfold markProduct
  convert h
private theorem coldWeight_nonneg (hR : Base R) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : 0 ≤ coldWeight R V Yt b p := by
  classical
  unfold coldWeight hullBaseDensity
  split_ifs with hh
  · exact mul_nonneg (mul_nonneg (hR.row.2.nonneg _ hside _ _ _ hh) (baseLaw_nonneg R _ _))
      (kernelProduct_nonneg hR _ _ _)
  · simp
private theorem sum_configurationWeight (hR : Base R) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :
    ∑ bad ∈ (markedBonds R (∅ : Finset (TorusSite n))).powerset, configurationWeight R ∅ V bad Yt b p.1 p.2 =
      ENNReal.ofReal (coldWeight R V Yt b p) := by
  classical
  by_cases hh : IsHullState R.params R.range p.1 Yt
  · have e : ∀ bad, configurationWeight R ∅ V bad Yt b p.1 p.2 =
        ENNReal.ofReal (coldWeight R V Yt b p * markProduct R ∅ V p.1 bad) := by
      intro bad
      unfold configurationWeight coldWeight hullBaseDensity kernelProduct stepWeight
      rw [if_pos hh, if_pos hh]
    simp only [e]
    rw [← ENNReal.ofReal_sum_of_nonneg fun bad _ =>
      mul_nonneg (coldWeight_nonneg hR hside V Yt b p) (markProduct_nonneg hR _ V _ bad), ← Finset.mul_sum,
      sum_markProduct, mul_one]
  · have e1 : ∀ bad, configurationWeight R ∅ V bad Yt b p.1 p.2 = 0 := fun bad => if_neg hh
    have e2 : coldWeight R V Yt b p = 0 := by
      unfold coldWeight hullBaseDensity
      rw [if_neg hh, zero_mul]
    simp [e1, e2]
private theorem measurable_coldWeight (hR : Base R) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n)
    (hw : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        configurationWeight R ∅ V bad Yt b p.1 p.2)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable (coldWeight R V Yt b) := by
  have e : coldWeight R V Yt b = fun p =>
      (∑ bad ∈ (markedBonds R (∅ : Finset (TorusSite n))).powerset,
        configurationWeight R ∅ V bad Yt b p.1 p.2).toReal := by
    funext p
    rw [sum_configurationWeight hR hside, ENNReal.toReal_ofReal (coldWeight_nonneg hR hside V Yt b p)]
  rw [e]
  exact (Finset.measurable_sum _ fun bad _ => hw bad Yt b).ennreal_toReal
private theorem caseIntegral_coldCaseGround (V : TorusField n) (F : CaseFunctional R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    (coldCaseGround R V).caseIntegral F bad Yt b =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, F W Yt ωt bad b * configurationWeight R ∅ V bad Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  unfold GasGround.caseIntegral
  refine lintegral_congr fun W => ?_
  have e : ∀ ν : (coldCaseGround R V).state.unlabelled Yt → R.labels.Ω,
      (coldCaseGround R V).caseIntegrand F bad Yt b W ν =
      (fun ωt : Yt → R.labels.Ω => F W Yt ωt bad b * configurationWeight R ∅ V bad Yt b W ωt)
        ((emptyCoarseState R).fillLabels Yt ν) := by
    intro ν
    unfold GasGround.caseIntegrand configurationWeight
    change (if IsHullState R.params R.range ((emptyCoarseState R).fieldWithStoredLinks W) Yt ∧
        coarseStateOf R ∅ ((emptyCoarseState R).fieldWithStoredLinks W) Yt
          ((emptyCoarseState R).fillLabels Yt ν) bad b = emptyCoarseState R then
        F ((emptyCoarseState R).fieldWithStoredLinks W) Yt ((emptyCoarseState R).fillLabels Yt ν) bad b *
          ENNReal.ofReal (stepWeight R ∅ V ((emptyCoarseState R).fieldWithStoredLinks W) Yt
            ((emptyCoarseState R).fillLabels Yt ν) bad b)
      else 0) = _
    rw [fieldWithStoredLinks_empty]
    by_cases h : IsHullState R.params R.range W Yt
    · rw [if_pos ⟨h, coarseStateOf_empty R W Yt _ bad b⟩]
      exact congrArg (fun z => F W Yt _ bad b * z) (if_pos h).symm
    · rw [if_neg fun c => h c.1]
      exact ((congrArg (fun z => F W Yt _ bad b * z) (if_neg h)).trans (mul_zero _)).symm
  simp only [e]
  exact lintegral_relabel R.labels.μ (unlabelled_empty R Yt) _ (fillLabels_empty R)
    (fun ωt : Yt → R.labels.Ω => F W Yt ωt bad b * configurationWeight R ∅ V bad Yt b W ωt)
private theorem caseMass_empty (G : GasGround R n) (F : CaseFunctional R n) :
    G.caseMass ∅ F = ∑ bad ∈ (markedBonds R G.cut).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n, G.caseIntegral F bad Yt b := by apply _root_.YangMills.SharedProofs.p25367 <;> assumption
private theorem caseMass_lift (hR : Base R) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n)
    (hw : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        configurationWeight R ∅ V bad Yt b p.1 p.2)
    (φ : (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
      TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ≥0∞)
    (hφ : ∀ Yt b, Measurable (φ Yt b)) :
    (coldCaseGround R V).caseMass ∅ (fun W Yt ωt _ b => φ Yt b (W, ωt)) = coldMass R V φ := by
  classical
  have h1 : ∀ bad Yt b, (coldCaseGround R V).caseIntegral (fun W Yt ωt _ b => φ Yt b (W, ωt)) bad Yt b =
      ∫⁻ p, φ Yt b p * configurationWeight R ∅ V bad Yt b p.1 p.2 ∂fieldLabelMeasure R n Yt := by
    intro bad Yt b
    have hm : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        φ Yt b p * configurationWeight R ∅ V bad Yt b p.1 p.2 :=
      (hφ Yt b).mul (hw bad Yt b)
    rw [caseIntegral_coldCaseGround, fieldLabelMeasure, lintegral_prod _ hm.aemeasurable]
  rw [caseMass_empty]
  show ∑ bad ∈ (markedBonds R (∅ : Finset (TorusSite n))).powerset,
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        (coldCaseGround R V).caseIntegral (fun W Yt ωt _ b => φ Yt b (W, ωt)) bad Yt b = _
  simp only [h1]
  unfold coldMass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← lintegral_finsetSum _ (f := fun bad p => φ Yt b p * configurationWeight R ∅ V bad Yt b p.1 p.2)
    fun bad _ => (hφ Yt b).mul (hw bad Yt b)]
  refine lintegral_congr fun p => ?_
  rw [← Finset.mul_sum, sum_configurationWeight hR hside]
private theorem coldMass_mono (V : TorusField n)
    {φ ψ : (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
      TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ≥0∞}
    (h : ∀ Yt b p, φ Yt b p ≤ ψ Yt b p) : coldMass R V φ ≤ coldMass R V ψ :=
  Finset.sum_le_sum fun Yt _ => Finset.sum_le_sum fun b _ => lintegral_mono fun p => by gcongr; exact h Yt b p
private theorem term_le_coldMass (V : TorusField n)
    (φ : (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
      TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ≥0∞)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    ∫⁻ p, φ Yt b p * ENNReal.ofReal (coldWeight R V Yt b p) ∂fieldLabelMeasure R n Yt ≤ coldMass R V φ :=
  (Finset.single_le_sum (f := fun b' => ∫⁻ p, φ Yt b' p * ENNReal.ofReal (coldWeight R V Yt b' p)
    ∂fieldLabelMeasure R n Yt) (fun _ _ => zero_le) (Finset.mem_univ b)).trans
  (Finset.single_le_sum (f := fun Yt' => ∑ b', ∫⁻ p, φ Yt' b' p * ENNReal.ofReal (coldWeight R V Yt' b' p)
    ∂fieldLabelMeasure R n Yt') (fun _ _ => zero_le) (Finset.mem_univ Yt))
private theorem integrable_coldIntegrand (hR : Base R) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n)
    (hw : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        configurationWeight R ∅ V bad Yt b p.1 p.2)
    {f : ColdFunction R n} (hf : ∀ Yt b, Measurable (f Yt b))
    (hfin : coldMass R V (fun Yt b p => ENNReal.ofReal |f Yt b p|) ≠ ⊤)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Integrable (coldIntegrand R V f Yt b) (fieldLabelMeasure R n Yt) := by
  have hm : Measurable (coldIntegrand R V f Yt b) := (hf Yt b).mul (measurable_coldWeight hR hside V hw Yt b)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  show ∫⁻ p, ‖coldIntegrand R V f Yt b p‖ₑ ∂fieldLabelMeasure R n Yt < ⊤
  have e : (fun p => ‖coldIntegrand R V f Yt b p‖ₑ) =
      fun p => ENNReal.ofReal |f Yt b p| * ENNReal.ofReal (coldWeight R V Yt b p) := by
    funext p
    show ‖f Yt b p * coldWeight R V Yt b p‖ₑ = _
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (coldWeight_nonneg hR hside V Yt b p),
      ENNReal.ofReal_mul (abs_nonneg _)]
  rw [e]
  exact lt_of_le_of_lt (term_le_coldMass V (fun Yt b p => ENNReal.ofReal |f Yt b p|) Yt b) hfin.lt_top
private theorem coldWeightedIntegral_eq (hR : Base R) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n)
    (hw : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        configurationWeight R ∅ V bad Yt b p.1 p.2)
    {f : ColdFunction R n} (hf : ∀ Yt b, Measurable (f Yt b))
    (hfin : coldMass R V (fun Yt b p => ENNReal.ofReal |f Yt b p|) ≠ ⊤) :
    coldWeightedIntegral R V f = (coldMass R V fun Yt b p => ENNReal.ofReal (f Yt b p)).toReal -
      (coldMass R V fun Yt b p => ENNReal.ofReal (-f Yt b p)).toReal := by
  have hT : ∀ Yt b, ∫ p, coldIntegrand R V f Yt b p ∂fieldLabelMeasure R n Yt =
      (∫⁻ p, ENNReal.ofReal (f Yt b p) * ENNReal.ofReal (coldWeight R V Yt b p) ∂fieldLabelMeasure R n Yt).toReal -
      (∫⁻ p, ENNReal.ofReal (-f Yt b p) * ENNReal.ofReal (coldWeight R V Yt b p)
        ∂fieldLabelMeasure R n Yt).toReal := by
    intro Yt b
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (integrable_coldIntegrand hR hside V hw hf hfin Yt b)]
    have e1 : ∀ p, ENNReal.ofReal (coldIntegrand R V f Yt b p) =
        ENNReal.ofReal (f Yt b p) * ENNReal.ofReal (coldWeight R V Yt b p) := fun p =>
      ENNReal.ofReal_mul' (coldWeight_nonneg hR hside V Yt b p)
    have e2 : ∀ p, ENNReal.ofReal (-coldIntegrand R V f Yt b p) =
        ENNReal.ofReal (-f Yt b p) * ENNReal.ofReal (coldWeight R V Yt b p) := fun p => by
      show ENNReal.ofReal (-(f Yt b p * coldWeight R V Yt b p)) = _
      rw [← neg_mul]
      exact ENNReal.ofReal_mul' (coldWeight_nonneg hR hside V Yt b p)
    simp only [e1, e2]
  have hle : ∀ (g : ℝ → ℝ), (∀ u, g u ≤ |u|) →
      coldMass R V (fun Yt b p => ENNReal.ofReal (g (f Yt b p))) ≠ ⊤ :=
    fun g hg => ne_top_of_le_ne_top hfin (coldMass_mono V fun Yt b p => ENNReal.ofReal_le_ofReal (hg _))
  have h1 : coldMass R V (fun Yt b p => ENNReal.ofReal (f Yt b p)) ≠ ⊤ := hle id fun u => le_abs_self u
  have h2 : coldMass R V (fun Yt b p => ENNReal.ofReal (-f Yt b p)) ≠ ⊤ := hle (fun u => -u) fun u => neg_le_abs u
  have hsum : ∀ {φ : (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
      TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ≥0∞},
      coldMass R V φ ≠ ⊤ → (coldMass R V φ).toReal =
        ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
          (∫⁻ p, φ Yt b p * ENNReal.ofReal (coldWeight R V Yt b p) ∂fieldLabelMeasure R n Yt).toReal := by
    intro φ hφ
    have h3 := ENNReal.sum_ne_top.mp hφ
    unfold coldMass
    rw [ENNReal.toReal_sum h3]
    refine Finset.sum_congr rfl fun Yt hY => ?_
    rw [ENNReal.toReal_sum (ENNReal.sum_ne_top.mp (h3 Yt hY))]
  rw [hsum h1, hsum h2]
  unfold coldWeightedIntegral
  simp only [hT, Finset.sum_sub_distrib]
end ColdCases
section Terms
variable {G : GasGround R n}
private theorem term_pos {H : CaseFunction R n} (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω)
    (hs : ∀ W' ωt, IsHullState R.params R.range W' Yt → 0 ≤ stepWeight R G.cut G.coarse W' Yt ωt bad b) :
    ENNReal.ofReal (caseTerm R G.cut G.coarse G.state H bad Yt b W ν) =
      G.caseIntegrand (weightBy (fun u => ENNReal.ofReal u) H) bad Yt b W ν := by
  classical
  unfold caseTerm GasGround.caseIntegrand weightBy
  split_ifs with hc
  · exact ENNReal.ofReal_mul' (hs _ (G.state.fillLabels Yt ν) hc.1)
  · simp
private theorem term_neg {H : CaseFunction R n} (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω)
    (hs : ∀ W' ωt, IsHullState R.params R.range W' Yt → 0 ≤ stepWeight R G.cut G.coarse W' Yt ωt bad b) :
    ENNReal.ofReal (-caseTerm R G.cut G.coarse G.state H bad Yt b W ν) =
      G.caseIntegrand (weightBy (fun u => ENNReal.ofReal (-u)) H) bad Yt b W ν := by
  classical
  unfold caseTerm GasGround.caseIntegrand weightBy
  split_ifs with hc
  · rw [← neg_mul]
    exact ENNReal.ofReal_mul' (hs _ (G.state.fillLabels Yt ν) hc.1)
  · simp
private theorem term_enorm {H : CaseFunction R n} (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω)
    (hs : ∀ W' ωt, IsHullState R.params R.range W' Yt → 0 ≤ stepWeight R G.cut G.coarse W' Yt ωt bad b) :
    ‖caseTerm R G.cut G.coarse G.state H bad Yt b W ν‖ₑ =
      G.caseIntegrand (weightBy (fun u => ENNReal.ofReal |u|) H) bad Yt b W ν := by apply _root_.YangMills.DeltaSharedProofs.p502092 <;> assumption
private theorem caseMass_mono {A : Finset (TorusSite n)} {F F' : CaseFunctional R n}
    (h : ∀ W Yt ωt bad b, F W Yt ωt bad b ≤ F' W Yt ωt bad b) : G.caseMass A F ≤ G.caseMass A F' := by
  classical
  unfold GasGround.caseMass
  refine Finset.sum_le_sum fun bad _ => Finset.sum_le_sum fun Yt _ => ?_
  split_ifs
  · refine Finset.sum_le_sum fun b _ => ?_
    unfold GasGround.caseIntegral
    refine lintegral_mono fun W => lintegral_mono fun ν => ?_
    unfold GasGround.caseIntegrand
    split_ifs
    · gcongr
      exact h _ _ _ _ _
    · exact le_rfl
  · exact le_rfl
private theorem caseIntegral_le_mass (F : CaseFunctional R n) {bad : Finset (TorusBond (n * R.params.side))}
    (hbad : bad ∈ (markedBonds R G.cut).powerset) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) : G.caseIntegral F bad Yt b ≤ G.caseMass ∅ F := by apply _root_.YangMills.SharedProofs.p5707 <;> assumption
private theorem term_integrable {H : CaseFunction R n} (hH : IsCaseReal H)
    (hBo : ∀ F : CaseFunctional R n, IsCaseFunctional F → ∀ (bad : Finset (TorusBond (n * R.params.side)))
      (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        G.caseIntegrand F bad Yt b p.1 p.2)
    (hfin : G.caseMass ∅ (weightBy (fun u => ENNReal.ofReal |u|) H) ≠ ⊤)
    {bad : Finset (TorusBond (n * R.params.side))} (hbad : bad ∈ (markedBonds R G.cut).powerset)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hs : ∀ W' ωt, IsHullState R.params R.range W' Yt → 0 ≤ stepWeight R G.cut G.coarse W' Yt ωt bad b) :
    Integrable (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2)
      ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := by
  classical
  have hm : Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
      caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2 := by
    have h1 := (hBo _ (isCaseFunctional_weightBy hH measurable_posPart) bad Yt b).ennreal_toReal
    have h2 := (hBo _ (isCaseFunctional_weightBy hH measurable_negPart) bad Yt b).ennreal_toReal
    have e : (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2) =
        fun p => (G.caseIntegrand (weightBy (fun u => ENNReal.ofReal u) H) bad Yt b p.1 p.2).toReal -
          (G.caseIntegrand (weightBy (fun u => ENNReal.ofReal (-u)) H) bad Yt b p.1 p.2).toReal := by
      funext p
      rw [← term_pos bad Yt b p.1 p.2 hs, ← term_neg bad Yt b p.1 p.2 hs, ENNReal.toReal_ofReal',
        ENNReal.toReal_ofReal']
      exact (max_zero_sub_max_neg_zero_eq_self _).symm
    rw [e]
    exact h1.sub h2
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  show ∫⁻ p, ‖caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2‖ₑ
    ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) < ⊤
  have e : (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
      ‖caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2‖ₑ) =
      fun p => G.caseIntegrand (weightBy (fun u => ENNReal.ofReal |u|) H) bad Yt b p.1 p.2 :=
    funext fun p => term_enorm bad Yt b p.1 p.2 hs
  rw [e, lintegral_prod _ (hBo _ (isCaseFunctional_weightBy hH measurable_absPart) bad Yt b).aemeasurable]
  exact lt_of_le_of_lt (caseIntegral_le_mass _ hbad Yt b) hfin.lt_top
private theorem caseIntegral_parts {H : CaseFunction R n} (hH : IsCaseReal H)
    (hBo : ∀ F : CaseFunctional R n, IsCaseFunctional F → ∀ (bad : Finset (TorusBond (n * R.params.side)))
      (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        G.caseIntegrand F bad Yt b p.1 p.2)
    (hfin : G.caseMass ∅ (weightBy (fun u => ENNReal.ofReal |u|) H) ≠ ⊤)
    (hs : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) W' ωt,
      IsHullState R.params R.range W' Yt → 0 ≤ stepWeight R G.cut G.coarse W' Yt ωt bad b) :
    caseIntegral R G.cut G.coarse G.state H = (G.caseMass ∅ (weightBy (fun u => ENNReal.ofReal u) H)).toReal -
      (G.caseMass ∅ (weightBy (fun u => ENNReal.ofReal (-u)) H)).toReal := by
  classical
  have hT : ∀ bad ∈ (markedBonds R G.cut).powerset, ∀ (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      ∫ W, ∫ ν : G.state.unlabelled Yt → R.labels.Ω, caseTerm R G.cut G.coarse G.state H bad Yt b W ν
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      (G.caseIntegral (weightBy (fun u => ENNReal.ofReal u) H) bad Yt b).toReal -
        (G.caseIntegral (weightBy (fun u => ENNReal.ofReal (-u)) H) bad Yt b).toReal := by
    intro bad hbad Yt b
    have hI := term_integrable hH hBo hfin hbad Yt b (hs bad Yt b)
    have e0 : ∫ W, ∫ ν : G.state.unlabelled Yt → R.labels.Ω, caseTerm R G.cut G.coarse G.state H bad Yt b W ν
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
        ∫ p, caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2
          ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) :=
      (integral_prod _ hI).symm
    rw [e0, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
    have e1 : (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        ENNReal.ofReal (caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2)) =
        fun p => G.caseIntegrand (weightBy (fun u => ENNReal.ofReal u) H) bad Yt b p.1 p.2 :=
      funext fun p => term_pos bad Yt b p.1 p.2 (hs bad Yt b)
    have e2 : (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        ENNReal.ofReal (-caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2)) =
        fun p => G.caseIntegrand (weightBy (fun u => ENNReal.ofReal (-u)) H) bad Yt b p.1 p.2 :=
      funext fun p => term_neg bad Yt b p.1 p.2 (hs bad Yt b)
    rw [e1, e2, lintegral_prod _ (hBo _ (isCaseFunctional_weightBy hH measurable_posPart) bad Yt b).aemeasurable,
      lintegral_prod _ (hBo _ (isCaseFunctional_weightBy hH measurable_negPart) bad Yt b).aemeasurable]
    rfl
  have hfp : G.caseMass ∅ (weightBy (fun u => ENNReal.ofReal u) H) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (caseMass_mono fun _ _ _ _ _ => ENNReal.ofReal_le_ofReal (le_abs_self _))
  have hfn : G.caseMass ∅ (weightBy (fun u => ENNReal.ofReal (-u)) H) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (caseMass_mono fun _ _ _ _ _ => ENNReal.ofReal_le_ofReal (neg_le_abs _))
  have hsum : ∀ {F : CaseFunctional R n}, G.caseMass ∅ F ≠ ⊤ → (G.caseMass ∅ F).toReal =
      ∑ bad ∈ (markedBonds R G.cut).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n, (G.caseIntegral F bad Yt b).toReal := by
    intro F hF
    rw [caseMass_empty] at hF ⊢
    have h3 := ENNReal.sum_ne_top.mp hF
    rw [ENNReal.toReal_sum h3]
    refine Finset.sum_congr rfl fun bad hb => ?_
    have h4 := ENNReal.sum_ne_top.mp (h3 bad hb)
    rw [ENNReal.toReal_sum h4]
    refine Finset.sum_congr rfl fun Yt hY => ?_
    rw [ENNReal.toReal_sum (ENNReal.sum_ne_top.mp (h4 Yt hY))]
  rw [hsum hfp, hsum hfn, ← Finset.sum_sub_distrib]
  unfold caseIntegral
  refine Finset.sum_congr rfl fun bad hb => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => hT bad hb Yt b
private def oneCase : CaseFunction R n := fun _ _ _ _ _ => 1
private theorem coarseStateWeight_eq (G : GasGround R n) :
    coarseStateWeight R G.cut G.coarse G.state =
      (G.caseMass ∅ (weightBy (fun u => ENNReal.ofReal u) oneCase)).toReal := by
  classical
  have e : coarseStateMass R G.cut G.coarse G.state = G.caseMass ∅ (weightBy (fun u => ENNReal.ofReal u) oneCase) := by
    rw [caseMass_empty]
    unfold coarseStateMass
    refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
    unfold GasGround.caseIntegral
    refine lintegral_congr fun W => lintegral_congr fun ν => ?_
    unfold GasGround.caseIntegrand
    split_ifs
    · show _ = ENNReal.ofReal 1 * _
      rw [ENNReal.ofReal_one, one_mul]
    · rfl
  unfold coarseStateWeight
  rw [e]
end Terms
section Means
variable {n' : ℕ} {free : Finset (TorusBond n')}
private theorem weightedMean_congr' {d G G' : FreeCoords free → ℝ} (h : ∀ η, d η ≠ 0 → G η = G' η) :
    weightedMean d G = weightedMean d G' := by apply _root_.YangMills.SharedProofs.p17143 <;> assumption
private theorem integrable_mul_of_bound {d G : FreeCoords free → ℝ} {M : ℝ} (hi : Integrable d)
    (hd : ∀ η, 0 ≤ d η) (hGm : Measurable G) (hG : ∀ η, d η ≠ 0 → |G η| ≤ M) :
    Integrable fun η => G η * d η := by apply _root_.YangMills.SharedProofs.p24304 <;> assumption
end Means
section Settings
private theorem chartDensity_nonneg (s : ChartSetting R n) (η : FreeCoords s.free) : 0 ≤ chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_nonneg <;> assumption
private theorem inBalls_of_chartDensity (s : ChartSetting R n) {η : FreeCoords s.free} (h : chartDensity s η ≠ 0) :
    s.InBalls η := by apply _root_.YangMills.SharedProofs.p4538 <;> assumption
private theorem isCold_trivialField (m : ℕ) {σ : ℝ} (hσ : 0 < σ) : IsCold σ (trivialField m) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
private theorem chartSetting_live (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hn : R.params.n₀ ≤ n)
    {s : ChartSetting R n} (hs : s.IsAdmissible) {η : FreeCoords s.free} (hη : s.InBalls η) :
    IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling := by apply _root_.YangMills.SharedProofs.p48283 <;> assumption
private theorem weightNorm_nonneg (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
private theorem siteScore_nonneg {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {m : ℕ} (Y : Finset (TorusSite m))
    (ω : Y → Ω) (y : TorusSite m) : 0 ≤ siteScore s Y ω y := by apply _root_.YangMills.SharedProofs.p22275 <;> assumption
end Settings
section Gas
private def inSetting (G : GasGround R n) (H : CaseFunction R n) (σ : G.Config)
    (η : FreeCoords (configSetting G σ).free) : ℝ :=
  H ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling (G.badBondsOf σ)
    (configSetting G σ).bases
private theorem gasIntegrand_eq (G : GasGround R n) (f : ℝ → ℝ≥0∞) (H : CaseFunction R n) {σ : G.Config}
    (ha : G.pairConstraint.IsAdmissible σ) :
    G.gasIntegrand (weightBy f H) σ =
      ∫⁻ η, f (inSetting G H σ η) * ENNReal.ofReal (chartDensity (configSetting G σ) η) :=
  if_pos ha
private structure GasFacts (G : GasGround R n) (z : G.GasSpin → ℝ) : Prop where
  weight : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z
  prob : IsProbabilityMeasure (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight)
  setting : ∀ σ, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible
  density_int : ∀ σ, G.pairConstraint.IsAdmissible σ → Integrable (chartDensity (configSetting G σ))
  density_pos : ∀ σ, G.pairConstraint.IsAdmissible σ → 0 < ∫ η, chartDensity (configSetting G σ) η
  mass : ∀ σ, G.pairConstraint.IsAdmissible σ →
    settingMass (configSetting G σ) = ENNReal.ofReal (∫ η, chartDensity (configSetting G σ) η)
  borel : ∀ F : CaseFunctional R n, IsCaseFunctional F → Measurable (G.gasIntegrand F)
variable {G : GasGround R n} {z : G.GasSpin → ℝ}
private theorem weight_eq (hf : GasFacts G z) {σ : G.Config} (ha : G.pairConstraint.IsAdmissible σ) :
    G.weight σ = ∫ η, chartDensity (configSetting G σ) η := by
  have e : G.weight σ = (settingMass (configSetting G σ)).toReal := if_pos ha
  rw [e, hf.mass σ ha, ENNReal.toReal_ofReal (integral_nonneg (chartDensity_nonneg _))]
private theorem weightDensity_eq (hf : GasFacts G z) {σ : G.Config} (ha : G.pairConstraint.IsAdmissible σ) :
    G.pairConstraint.weightDensity G.weight σ = settingMass (configSetting G σ) := by
  have e : G.pairConstraint.weightDensity G.weight σ = ENNReal.ofReal (G.weight σ) := if_pos ha
  rw [e, weight_eq hf ha, hf.mass σ ha]
private theorem total_facts (hf : GasFacts G z) :
    ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) ≠ 0 ∧
      ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) ≠ ⊤ := by
  have h1 : G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight Set.univ = 1 := hf.prob.measure_univ
  simp only [PairConstraint.gibbsLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h1
  constructor
  · intro h0
    rw [h0] at h1
    simp at h1
  · intro h0
    rw [h0] at h1
    simp at h1
private theorem ae_admissible (hf : GasFacts G z) : ∀ᵐ σ ∂G.gibbsLaw ∅, G.pairConstraint.IsAdmissible σ := by
  rw [ae_iff]
  have hs : MeasurableSet {σ | ¬ G.pairConstraint.IsAdmissible σ} := hf.weight.measurableSet_admissible.compl
  show G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight _ = 0
  simp only [PairConstraint.gibbsLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
  have : ∫⁻ σ in {σ | ¬ G.pairConstraint.IsAdmissible σ}, G.pairConstraint.weightDensity G.weight σ
      ∂Measure.pi (G.referenceMeasure ∅) = 0 := by
    have hz : ∀ σ ∈ {σ | ¬ G.pairConstraint.IsAdmissible σ},
        G.pairConstraint.weightDensity G.weight σ = (fun _ => (0 : ℝ≥0∞)) σ :=
      fun σ hσ => if_neg hσ
    rw [setLIntegral_congr_fun hs hz]
    simp
  rw [this, mul_zero]
private theorem integral_parts (hf : GasFacts G z) (H : CaseFunction R n) {σ : G.Config}
    (ha : G.pairConstraint.IsAdmissible σ)
    (hI : Integrable fun η => inSetting G H σ η * chartDensity (configSetting G σ) η) :
    ∫ η, inSetting G H σ η * chartDensity (configSetting G σ) η =
      (G.gasIntegrand (weightBy (fun u => ENNReal.ofReal u) H) σ).toReal -
        (G.gasIntegrand (weightBy (fun u => ENNReal.ofReal (-u)) H) σ).toReal := by
  rw [gasIntegrand_eq G _ H ha, gasIntegrand_eq G _ H ha, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
  have e1 : ∀ η, ENNReal.ofReal (inSetting G H σ η * chartDensity (configSetting G σ) η) =
      ENNReal.ofReal (inSetting G H σ η) * ENNReal.ofReal (chartDensity (configSetting G σ) η) := fun η =>
    ENNReal.ofReal_mul' (chartDensity_nonneg _ η)
  have e2 : ∀ η, ENNReal.ofReal (-(inSetting G H σ η * chartDensity (configSetting G σ) η)) =
      ENNReal.ofReal (-inSetting G H σ η) * ENNReal.ofReal (chartDensity (configSetting G σ) η) := fun η => by
    rw [← neg_mul]
    exact ENNReal.ofReal_mul' (chartDensity_nonneg _ η)
  simp only [e1, e2]
private theorem gasIntegrand_ne_top (hf : GasFacts G z) (H : CaseFunction R n) {σ : G.Config}
    (ha : G.pairConstraint.IsAdmissible σ)
    (hI : Integrable fun η => inSetting G H σ η * chartDensity (configSetting G σ) η) :
    G.gasIntegrand (weightBy (fun u => ENNReal.ofReal u) H) σ ≠ ⊤ ∧
      G.gasIntegrand (weightBy (fun u => ENNReal.ofReal (-u)) H) σ ≠ ⊤ := by
  rw [gasIntegrand_eq G _ H ha, gasIntegrand_eq G _ H ha]
  have e1 : ∀ η, ENNReal.ofReal (inSetting G H σ η) * ENNReal.ofReal (chartDensity (configSetting G σ) η) =
      ENNReal.ofReal (inSetting G H σ η * chartDensity (configSetting G σ) η) := fun η =>
    (ENNReal.ofReal_mul' (chartDensity_nonneg _ η)).symm
  have e2 : ∀ η, ENNReal.ofReal (-inSetting G H σ η) * ENNReal.ofReal (chartDensity (configSetting G σ) η) =
      ENNReal.ofReal (-(inSetting G H σ η * chartDensity (configSetting G σ) η)) := fun η => by
    rw [← neg_mul]
    exact (ENNReal.ofReal_mul' (chartDensity_nonneg _ η)).symm
  simp only [e1, e2]
  exact ⟨hI.lintegral_lt_top.ne, hI.neg.lintegral_lt_top.ne⟩
private theorem gasMass_le (hf : GasFacts G z) {H : CaseFunction R n} {B : G.Config → ℝ≥0∞}
    (hB : ∀ (σ : G.Config) η, G.pairConstraint.IsAdmissible σ → ENNReal.ofReal |inSetting G H σ η| ≤ B σ) :
    G.gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|) H) ≤
      ∫⁻ σ, B σ * G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) := by
  refine lintegral_mono fun σ => ?_
  by_cases ha : G.pairConstraint.IsAdmissible σ
  · rw [gasIntegrand_eq G _ _ ha, weightDensity_eq hf ha]
    have hae : AEMeasurable fun η => ENNReal.ofReal (chartDensity (configSetting G σ) η) :=
      (hf.density_int σ ha).aemeasurable.ennreal_ofReal
    calc ∫⁻ η, ENNReal.ofReal |inSetting G H σ η| * ENNReal.ofReal (chartDensity (configSetting G σ) η)
        ≤ ∫⁻ η, B σ * ENNReal.ofReal (chartDensity (configSetting G σ) η) :=
          lintegral_mono fun η => by gcongr; exact hB σ η ha
      _ = B σ * settingMass (configSetting G σ) := lintegral_const_mul'' _ hae
  · have e : G.gasIntegrand (weightBy (fun u => ENNReal.ofReal |u|) H) σ = 0 := if_neg ha
    rw [e]
    exact zero_le
private theorem gasMass_one (hf : GasFacts G z) :
    G.gasMass ∅ (weightBy (fun u => ENNReal.ofReal u) oneCase) = G.partitionFunction ∅ := by
  refine lintegral_congr fun σ => ?_
  by_cases ha : G.pairConstraint.IsAdmissible σ
  · rw [gasIntegrand_eq G _ _ ha, weightDensity_eq hf ha]
    show ∫⁻ η, ENNReal.ofReal 1 * _ = ∫⁻ η, _
    simp only [ENNReal.ofReal_one, one_mul]
    rfl
  · have e1 : G.gasIntegrand (weightBy (fun u => ENNReal.ofReal u) oneCase) σ = 0 := if_neg ha
    have e2 : G.pairConstraint.weightDensity G.weight σ = 0 := if_neg ha
    rw [e1, e2]
end Gas
section AllVacant
variable {G : GasGround R n}
private theorem familyOf_allVacant (G : GasGround R n) : G.familyOf G.allVacant = GasFamily.empty := by
  classical
  funext θ
  unfold GasGround.familyOf
  split_ifs <;> rfl
abbrev _root_.YangMills.SharedProofs.p24466 := @familyOf_allVacant
private theorem configSetting_allVacant (G : GasGround R n) : configSetting G G.allVacant = G.groundSetting := by apply _root_.YangMills.DeltaSharedProofs.p176 <;> assumption
private theorem isAdmissible_allVacant (G : GasGround R n) : G.pairConstraint.IsAdmissible G.allVacant :=
  fun _ _ _ => Or.inl rfl
private theorem spin_touches (i : G.GasSpin) : i.1.Touches Finset.univ := by
  classical
  obtain ⟨w, hw⟩ := i.2.isCluster.1
  rcases Finset.mem_union.mp hw with h | h
  · obtain ⟨b, hb, -⟩ := Finset.mem_image.mp h
    exact Or.inl ⟨b, hb, Finset.mem_univ _⟩
  · exact Or.inr ⟨w, h, Finset.mem_univ _⟩
private theorem pi_referenceMeasure_univ (G : GasGround R n) :
    Measure.pi (G.referenceMeasure Finset.univ) = Measure.dirac G.allVacant := by
  classical
  have hr : ∀ i : G.GasSpin, G.referenceMeasure Finset.univ i = Measure.dirac (Sum.inl () : G.SpinValue i) := by
    intro i
    unfold GasGround.referenceMeasure GasGround.referenceMeasureOff
    rw [if_pos (spin_touches i)]
    refine Measure.ext fun t ht => ?_
    rw [Measure.map_apply measurable_inl ht, Measure.dirac_apply' _ (measurable_inl ht), Measure.dirac_apply' _ ht]
    rfl
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp only [hr, Measure.dirac_apply' _ (hs _)]
  by_cases h : G.allVacant ∈ Set.pi Set.univ s
  · rw [Set.indicator_of_mem h]
    symm
    refine Finset.prod_eq_one fun i _ => ?_
    exact Set.indicator_of_mem (h i (Set.mem_univ i)) _
  · rw [Set.indicator_of_notMem h]
    symm
    obtain ⟨i, hi⟩ : ∃ i, G.allVacant i ∉ s i := by
      by_contra hc
      push Not at hc
      exact h fun i _ => hc i
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
private theorem gasMass_univ (G : GasGround R n) (F : CaseFunctional R n) (hF : Measurable (G.gasIntegrand F)) :
    G.gasMass Finset.univ F = G.gasIntegrand F G.allVacant := by
  unfold GasGround.gasMass
  rw [pi_referenceMeasure_univ, lintegral_dirac' _ hF]
private theorem partitionFunction_univ (G : GasGround R n)
    (hd : Measurable (G.pairConstraint.weightDensity G.weight)) :
    G.partitionFunction Finset.univ = G.pairConstraint.weightDensity G.weight G.allVacant := by
  unfold GasGround.partitionFunction
  rw [pi_referenceMeasure_univ, lintegral_dirac' _ hd]
end AllVacant
section Centred
private theorem isCold_of_isHullState_empty (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hfit : ℓ.Admissible) {m : ℕ} [NeZero m]
    (hLn : ℓ.side ∣ m) (r : ℕ) (W : TorusField m) (h : IsHullState ℓ r W ∅) : IsCold ℓ.threshold W := by apply _root_.YangMills.Construction.MarkedIntegrals.MarkedIntegralIdentity.isCold_of_isHullState <;> assumption
private theorem baseChoices_of_isCold (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (hW : IsCold ℓ.threshold W) :
    baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) = {fun y => cellCentre 0 y} := by apply _root_.YangMills.Construction.MarkedIntegrals.MarkedIntegralIdentity.baseChoices_eq_singleton <;> assumption
private theorem eq_centreBases_of_baseLaw (hfit : R.params.Admissible) {W : TorusField (n * R.params.side)}
    (hh : IsHullState R.params R.range W ∅) {b : BaseChoice R.params.side n} (hb : baseLaw (R := R) W b ≠ 0) :
    b = centreBases R.params.side n := by
  classical
  have hc : IsCold R.params.threshold W :=
    isCold_of_isHullState_empty R.params hfit (Dvd.intro_left n rfl) _ W hh
  unfold baseLaw at hb
  split_ifs at hb with h
  · rw [baseChoices_of_isCold R.params W hc] at h
    exact Finset.mem_singleton.mp h
  · exact absurd rfl hb
private theorem sitesInBlocks_univ (L : ℕ) [NeZero L] :
    sitesInBlocks L (Finset.univ : Finset (TorusSite n)) = Finset.univ := by apply _root_.YangMills.Construction.MarkedIntegrals.MarkedIntegralIdentity.sitesInBlocks_univ <;> assumption
open Classical in
private theorem avoidingPart_univ (R : StepSetup) (hrow : R.HasExpansions)
    (hb : IsBlockTorusSide R.params (n * R.params.side)) (W : TorusField (n * R.params.side)) :
    R.avoidingPart Finset.univ W =
      if IsHullState R.params R.range W ∅ then R.labelWeight (n * R.params.side) W ∅ (emptyLabeling R) else 0 := by
  unfold StepSetup.avoidingPart
  have hset : ((Finset.univ : Finset (Finset (TorusSite (n * R.params.side)))).filter fun Y =>
      IsHullState R.params R.range W Y ∧
        Disjoint Y (sitesInBlocks R.params.side (Finset.univ : Finset (TorusSite n)))) =
      if IsHullState R.params R.range W ∅ then {∅} else ∅ := by
    ext Y
    rw [sitesInBlocks_univ, ← Finset.top_eq_univ]
    simp only [Finset.mem_filter, Finset.top_eq_univ, Finset.mem_univ, true_and]
    rw [← Finset.top_eq_univ, disjoint_top, Finset.bot_eq_empty]
    split_ifs with h
    · simp only [Finset.mem_singleton]
      exact ⟨fun q => q.2, fun q => by rw [q]; exact ⟨h, rfl⟩⟩
    · simp only [Finset.notMem_empty, iff_false]
      rintro ⟨q1, rfl⟩
      exact h q1
  rw [hset]
  split_ifs with h
  · rw [Finset.sum_singleton]
    have hempty : (Measure.pi fun _ : ↥(∅ : Finset (TorusSite (n * R.params.side))) => R.labels.μ) =
        Measure.dirac (emptyLabeling R) := Measure.pi_of_empty _ _
    rw [hempty, lintegral_dirac' _ ?_, ENNReal.toReal_ofReal (hrow.2.nonneg _ hb W ∅ _ h)]
    exact measurable_const' fun a b => by rw [Subsingleton.elim a b]
  · simp
private theorem markProduct_empty (V : TorusField n) (W : TorusField (n * R.params.side)) :
    markProduct R ∅ V W ∅ =
      ∏ b ∈ chartBondsInBlocks R.params.side (Finset.univ : Finset (TorusSite n)), R.bondMark V W b := by
  classical
  unfold markProduct chartBondsInBlocks
  rw [markedBonds_empty]
  simp only [Finset.notMem_empty, if_false, Finset.mem_univ, Finset.filter_true]
  rfl
private theorem caseAvoids_univ (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) :
    (coldCaseGround R V).CaseAvoids Finset.univ bad Yt ↔ bad = ∅ ∧ Yt = ∅ := by
  unfold GasGround.CaseAvoids
  rw [recordedBad_cold, recordedSites_cold]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Finset.eq_empty_of_forall_notMem fun c hc => h1 c hc (Finset.notMem_empty _) (Finset.mem_univ _),
      Finset.eq_empty_of_forall_notMem fun w hw => h2 w hw (Finset.notMem_empty _) (Finset.mem_univ _)⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Finset.notMem_empty _)⟩
end Centred
section ColdFacts
private structure ColdFacts (R : StepSetup) {n : ℕ} [NeZero n] (V : TorusField n)
    (z : (coldCaseGround R V).GasSpin → ℝ) : Prop where
  base : Base R
  side : IsBlockTorusSide R.params (n * R.params.side)
  floor : R.params.n₀ ≤ n
  weights : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n),
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      configurationWeight R ∅ V bad Yt b p.1 p.2
  gas : GasFacts (coldCaseGround R V) z
  cases : ∀ F : CaseFunctional R n, IsCaseFunctional F → ∀ (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
    Measurable fun p : TorusField (n * R.params.side) × ((coldCaseGround R V).state.unlabelled Yt → R.labels.Ω) =>
      (coldCaseGround R V).caseIntegrand F bad Yt b p.1 p.2
  image : ∀ (A : Finset (TorusSite n)) (F : CaseFunctional R n), IsCaseFunctional F →
    (coldCaseGround R V).caseMass A F =
      ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
        (coldCaseGround R V).gasMass A F
  mean : ∀ F : CaseFunction R n,
    (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) →
    IsGaugeInvariantCase F → CaseIntegrable R ∅ V (emptyCoarseState R) F →
    caseMean R ∅ V (emptyCoarseState R) F = gasExpectationOfCase (coldCaseGround R V) F
  D_pos : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side))
  marked : R.markedIntegral Finset.univ V =
    R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
      ((coldCaseGround R V).partitionFunction Finset.univ).toReal
variable {V : TorusField n} {z : (coldCaseGround R V).GasSpin → ℝ}
private theorem stepWeight_nonneg (hC : ColdFacts R V z) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω) (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R ∅ V W Yt ωt bad b :=
  mul_nonneg (mul_nonneg (mul_nonneg (hC.base.row.2.nonneg _ hC.side W Yt ωt hh) (baseLaw_nonneg R W b))
    (kernelProduct_nonneg hC.base W V b)) (markProduct_nonneg hC.base ∅ V W bad)
private theorem isCaseReal_one : IsCaseReal (oneCase : CaseFunction R n) :=
  ⟨fun _ _ _ => measurable_const, fun _ _ _ _ _ _ _ _ _ => rfl⟩
private theorem caseMass_ne_top (hC : ColdFacts R V z) {H : CaseFunction R n} (hH : IsCaseReal H)
    (h : (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|) H) ≠ ⊤) :
    (coldCaseGround R V).caseMass ∅ (weightBy (fun u => ENNReal.ofReal |u|) H) ≠ ⊤ := by
  rw [hC.image _ _ (isCaseFunctional_weightBy hH measurable_absPart)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h
private theorem coldMass_eq (hC : ColdFacts R V z) {f : ColdFunction R n} (hf : ∀ Yt b, Measurable (f Yt b))
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    (coldCaseGround R V).caseMass ∅ (weightBy φ (lift f)) = coldMass R V fun Yt b p => φ (f Yt b p) := by
  have e : weightBy φ (lift f) = fun W Yt ωt _ b => (fun Yt b p => φ (f Yt b p)) Yt b (W, ωt) := rfl
  rw [e]
  exact caseMass_lift hC.base hC.side V hC.weights (fun Yt b p => φ (f Yt b p)) fun Yt b => hφ.comp (hf Yt b)
private theorem coldMass_ne_top (hC : ColdFacts R V z) {f : ColdFunction R n} (hH : IsCaseReal (lift f))
    (h : (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|) (lift f)) ≠ ⊤) :
    coldMass R V (fun Yt b p => ENNReal.ofReal |f Yt b p|) ≠ ⊤ := fun ht =>
  caseMass_ne_top hC hH h ((coldMass_eq hC (fun Yt b => hH.borel Yt ∅ b) measurable_absPart).trans ht)
private theorem coldWeightedIntegral_lift (hC : ColdFacts R V z) {f : ColdFunction R n} (hH : IsCaseReal (lift f))
    (hfin : (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|) (lift f)) ≠ ⊤) :
    coldWeightedIntegral R V f = caseIntegral R ∅ V (emptyCoarseState R) (lift f) := by
  have hf : ∀ Yt b, Measurable (f Yt b) := fun Yt b => hH.borel Yt ∅ b
  have h1 := caseIntegral_parts (G := coldCaseGround R V) hH hC.cases (caseMass_ne_top hC hH hfin)
    (fun bad Yt b W ωt hh => stepWeight_nonneg hC bad Yt b W ωt hh)
  have h2 := coldWeightedIntegral_eq hC.base hC.side V hC.weights hf (coldMass_ne_top hC hH hfin)
  rw [h2]
  refine Eq.trans ?_ h1.symm
  rw [coldMass_eq hC hf measurable_posPart, coldMass_eq hC hf measurable_negPart]
private theorem gas_const_ne_top (hC : ColdFacts R V z) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    ∫⁻ σ, (fun _ => c) σ * (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ
      ∂Measure.pi ((coldCaseGround R V).referenceMeasure ∅) ≠ ⊤ := by
  rw [lintegral_const_mul _ hC.gas.weight.measurable_weightDensity]
  exact ENNReal.mul_ne_top hc (total_facts hC.gas).2
private theorem gas_one_ne_top (hC : ColdFacts R V z) :
    (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|) (oneCase : CaseFunction R n)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (gas_const_ne_top hC (c := 1) ENNReal.one_ne_top) (gasMass_le hC.gas fun σ η _ => ?_)
  show ENNReal.ofReal |(1 : ℝ)| ≤ 1
  simp
private theorem coldWeightedIntegral_one (hC : ColdFacts R V z) :
    coldWeightedIntegral R V (fun _ _ _ => 1) = coarseStateWeight R ∅ V (emptyCoarseState R) := by
  have hf : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable ((fun _ _ _ => 1 : ColdFunction R n) Yt b) := fun _ _ => measurable_const
  have h2 := coldWeightedIntegral_eq hC.base hC.side V hC.weights hf
    (coldMass_ne_top hC (f := fun _ _ _ => 1) isCaseReal_one (gas_one_ne_top hC))
  have h0 : ENNReal.ofReal (-1) = 0 := ENNReal.ofReal_of_nonpos (by norm_num)
  have h3 : (coldMass R V fun Yt b p => ENNReal.ofReal (-(fun _ _ _ => 1 : ColdFunction R n) Yt b p)) = 0 := by
    unfold coldMass
    simp only [h0, zero_mul, lintegral_zero, Finset.sum_const_zero]
  rw [h2, h3, ENNReal.toReal_zero, sub_zero]
  have h4 := coarseStateWeight_eq (coldCaseGround R V)
  refine Eq.trans ?_ h4.symm
  rw [show (oneCase : CaseFunction R n) = lift fun _ _ _ => 1 from rfl, coldMass_eq hC hf measurable_posPart]
private theorem coldWeightedIntegral_one_pos (hC : ColdFacts R V z) :
    0 < coldWeightedIntegral R V (fun _ _ _ => 1) := by
  rw [coldWeightedIntegral_one hC]
  have h4 := coarseStateWeight_eq (coldCaseGround R V)
  rw [hC.image _ _ (isCaseFunctional_weightBy isCaseReal_one measurable_posPart), gasMass_one hC.gas] at h4
  refine lt_of_lt_of_eq ?_ h4.symm
  exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.mpr hC.D_pos).ne' (total_facts hC.gas).1)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (total_facts hC.gas).2)
private theorem coldExpectation_lift (hC : ColdFacts R V z) {f : ColdFunction R n} (hH : IsCaseReal (lift f))
    (hfin : (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|) (lift f)) ≠ ⊤) :
    (∀ Yt b, Integrable (coldIntegrand R V f Yt b) (fieldLabelMeasure R n Yt)) ∧
      coldExpectation R V f = gasExpectationOfCase (coldCaseGround R V) (lift f) := by
  refine ⟨integrable_coldIntegrand hC.base hC.side V hC.weights (fun Yt b => hH.borel Yt ∅ b)
    (coldMass_ne_top hC hH hfin), ?_⟩
  have hCI : CaseIntegrable R ∅ V (emptyCoarseState R) (lift f) := fun bad hbad Yt b =>
    term_integrable (G := coldCaseGround R V) hH hC.cases (caseMass_ne_top hC hH hfin) hbad Yt b
      fun W ωt hh => stepWeight_nonneg hC bad Yt b W ωt hh
  rw [← hC.mean _ hH.borel hH.gauge hCI]
  unfold coldExpectation caseMean
  rw [coldWeightedIntegral_lift hC hH hfin, coldWeightedIntegral_one hC]
private theorem caseMass_univ (hC : ColdFacts R V z) (F : CaseFunctional R n) (hF : IsCaseFunctional F) :
    (coldCaseGround R V).caseMass Finset.univ F = ∫⁻ W, ∑ b : BaseChoice R.params.side n,
      F W ∅ (emptyLabeling R) ∅ b * configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R)
        ∂fieldHaar (n * R.params.side) := by
  classical
  have hemp : ∀ b, (coldCaseGround R V).caseIntegral F ∅ ∅ b =
      ∫⁻ W, F W ∅ (emptyLabeling R) ∅ b * configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R)
        ∂fieldHaar (n * R.params.side) := by
    intro b
    rw [caseIntegral_coldCaseGround]
    refine lintegral_congr fun W => ?_
    have hempty : (Measure.pi fun _ : ↥(∅ : Finset (TorusSite (n * R.params.side))) => R.labels.μ) =
        Measure.dirac (emptyLabeling R) := Measure.pi_of_empty _ _
    rw [hempty, lintegral_dirac' _ ?_]
    exact measurable_const' fun a b => by rw [Subsingleton.elim a b]
  have hm : ∀ b, Measurable fun W : TorusField (n * R.params.side) =>
      F W ∅ (emptyLabeling R) ∅ b * configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R) := fun b =>
    ((hF.measurable ∅ ∅ b).mul (hC.weights ∅ ∅ b)).comp measurable_prodMk_right
  rw [lintegral_finsetSum _ fun b _ => hm b]
  unfold GasGround.caseMass
  rw [Finset.sum_eq_single ∅, Finset.sum_eq_single ∅, if_pos ((caseAvoids_univ V ∅ ∅).mpr ⟨rfl, rfl⟩)]
  · exact Finset.sum_congr rfl fun b _ => hemp b
  · intro Yt _ hY
    exact if_neg fun h => hY ((caseAvoids_univ V _ _).mp h).2
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro bad _ hb
    exact Finset.sum_eq_zero fun Yt _ => if_neg fun h => hb ((caseAvoids_univ V _ _).mp h).1
  · intro h
    exact absurd (Finset.empty_mem_powerset _) h
open Classical in
private theorem sum_at_empty (hC : ColdFacts R V z) {H : CaseFunction R n} {g : TorusField (n * R.params.side) → ℝ}
    (hg : ∀ W b, IsHullState R.params R.range W ∅ → baseLaw (R := R) W b ≠ 0 →
      H W ∅ (emptyLabeling R) ∅ b = g W)
    (φ : ℝ → ℝ≥0∞) (W : TorusField (n * R.params.side)) :
    ∑ b : BaseChoice R.params.side n, weightBy φ H W ∅ (emptyLabeling R) ∅ b *
        configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R) =
      if IsHullState R.params R.range W ∅ then
        φ (g W) * ENNReal.ofReal (R.labelWeight (n * R.params.side) W ∅ (emptyLabeling R) *
          averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
            (readAtLevel (stepBlockFrame R.params.side n) 1 V) * markProduct R ∅ V W ∅)
      else 0 := by
  by_cases hh : IsHullState R.params R.range W ∅
  · rw [if_pos hh]
    have hD := hC.base.row.2.nonneg _ hC.side W ∅ (emptyLabeling R) hh
    have hm := markProduct_nonneg hC.base ∅ V W ∅
    have e : ∀ b, weightBy φ H W ∅ (emptyLabeling R) ∅ b * configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R) =
        φ (g W) * ENNReal.ofReal (R.labelWeight (n * R.params.side) W ∅ (emptyLabeling R) *
          (baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
            bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
              (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
          markProduct R ∅ V W ∅) := by
      intro b
      have e1 : configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R) =
          ENNReal.ofReal (R.labelWeight (n * R.params.side) W ∅ (emptyLabeling R) *
            (baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
              bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
                (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
            markProduct R ∅ V W ∅) := by
        unfold configurationWeight stepWeight
        rw [if_pos hh]
        congr 1
        ring
      rw [e1]
      by_cases hb : baseLaw (R := R) W b = 0
      · simp [hb]
      · show φ (H W ∅ (emptyLabeling R) ∅ b) * _ = _
        rw [hg W b hh hb]
    have hk : ∀ b : BaseChoice R.params.side n, 0 ≤ ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c :=
      fun b => kernelProduct_nonneg hC.base W V b
    simp only [e]
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg fun b _ => mul_nonneg (mul_nonneg hD
      (mul_nonneg (baseLaw_nonneg R W b) (hk b))) hm, ← Finset.sum_mul, ← Finset.mul_sum, ← averagedKernel_eq]
  · rw [if_neg hh]
    refine Finset.sum_eq_zero fun b _ => ?_
    have e : configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R) = 0 := if_neg hh
    rw [e, mul_zero]
private theorem fullyMarkedExpectation_eq (hC : ColdFacts R V z) {H : CaseFunction R n} (hH : IsCaseReal H)
    {g : TorusField (n * R.params.side) → ℝ}
    (hg : ∀ W b, IsHullState R.params R.range W ∅ → baseLaw (R := R) W b ≠ 0 →
      H W ∅ (emptyLabeling R) ∅ b = g W)
    (hI : Integrable fun η => inSetting (coldCaseGround R V) H (coldCaseGround R V).allVacant η *
      chartDensity (configSetting (coldCaseGround R V) (coldCaseGround R V).allVacant) η) :
    fullyMarkedExpectation R V g =
      weightedMean (chartDensity (configSetting (coldCaseGround R V) (coldCaseGround R V).allVacant))
        (inSetting (coldCaseGround R V) H (coldCaseGround R V).allVacant) := by
  classical
  have ha := isAdmissible_allVacant (coldCaseGround R V)
  have hFp := isCaseFunctional_weightBy hH measurable_posPart
  have hFn := isCaseFunctional_weightBy hH measurable_negPart
  have hmA : ∀ {F : CaseFunctional R n}, IsCaseFunctional F →
      Measurable fun W : TorusField (n * R.params.side) => ∑ b : BaseChoice R.params.side n,
        F W ∅ (emptyLabeling R) ∅ b * configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R) := fun hF =>
    Finset.measurable_sum _ fun b _ =>
      ((hF.measurable ∅ ∅ b).mul (hC.weights ∅ ∅ b)).comp measurable_prodMk_right
  have hcA : ∀ {F : CaseFunctional R n}, IsCaseFunctional F → ∫⁻ W, ∑ b : BaseChoice R.params.side n,
      F W ∅ (emptyLabeling R) ∅ b * configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R)
        ∂fieldHaar (n * R.params.side) =
      ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
        (coldCaseGround R V).gasIntegrand F (coldCaseGround R V).allVacant :=
    fun {F} hF => by
      rw [← caseMass_univ hC F hF, hC.image _ _ hF, gasMass_univ _ _ (hC.gas.borel _ hF)]
  obtain ⟨hfp, hfn⟩ := gasIntegrand_ne_top hC.gas H ha hI
  have hip := ENNReal.mul_ne_top
    (ENNReal.ofReal_ne_top (r := R.functional (n * R.params.side) (trivialField (n * R.params.side)))) hfp
  have hin := ENNReal.mul_ne_top
    (ENNReal.ofReal_ne_top (r := R.functional (n * R.params.side) (trivialField (n * R.params.side)))) hfn
  rw [← hcA hFp] at hip
  rw [← hcA hFn] at hin
  have hpt : (fun W : TorusField (n * R.params.side) => R.avoidingPart Finset.univ W *
      averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) * g W *
      ∏ b ∈ chartBondsInBlocks R.params.side (Finset.univ : Finset (TorusSite n)), R.bondMark V W b) = fun W =>
      (∑ b : BaseChoice R.params.side n, weightBy (fun u => ENNReal.ofReal u) H W ∅ (emptyLabeling R) ∅ b *
        configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R)).toReal -
      (∑ b : BaseChoice R.params.side n, weightBy (fun u => ENNReal.ofReal (-u)) H W ∅ (emptyLabeling R) ∅ b *
        configurationWeight R ∅ V ∅ ∅ b W (emptyLabeling R)).toReal := by
    funext W
    rw [sum_at_empty hC hg, sum_at_empty hC hg, avoidingPart_univ R hC.base.row hC.side, ← markProduct_empty]
    by_cases hh : IsHullState R.params R.range W ∅
    · rw [if_pos hh, if_pos hh, if_pos hh]
      have hc : 0 ≤ R.labelWeight (n * R.params.side) W ∅ (emptyLabeling R) *
          averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
            (readAtLevel (stepBlockFrame R.params.side n) 1 V) * markProduct R ∅ V W ∅ := by
        refine mul_nonneg (mul_nonneg (hC.base.row.2.nonneg _ hC.side W ∅ (emptyLabeling R) hh) ?_)
          (markProduct_nonneg hC.base ∅ V W ∅)
        rw [averagedKernel_eq]
        exact Finset.sum_nonneg fun b _ => mul_nonneg (baseLaw_nonneg R W b) (kernelProduct_nonneg hC.base W V b)
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal',
        ENNReal.toReal_ofReal', ← sub_mul, max_zero_sub_max_neg_zero_eq_self]
      ring
    · rw [if_neg hh, if_neg hh, if_neg hh]
      simp
  have hnum : ∫ W : TorusField (n * R.params.side), R.avoidingPart Finset.univ W *
      averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) * g W *
      ∏ b ∈ chartBondsInBlocks R.params.side (Finset.univ : Finset (TorusSite n)), R.bondMark V W b
        ∂(fieldHaar (n * R.params.side)) =
      R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
        ((coldCaseGround R V).gasIntegrand (weightBy (fun u => ENNReal.ofReal u) H)
          (coldCaseGround R V).allVacant).toReal -
      R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
        ((coldCaseGround R V).gasIntegrand (weightBy (fun u => ENNReal.ofReal (-u)) H)
          (coldCaseGround R V).allVacant).toReal := by
    rw [hpt, integral_sub (integrable_toReal_of_lintegral_ne_top (hmA hFp).aemeasurable hip)
      (integrable_toReal_of_lintegral_ne_top (hmA hFn).aemeasurable hin),
      integral_toReal (hmA hFp).aemeasurable (ae_lt_top (hmA hFp) hip),
      integral_toReal (hmA hFn).aemeasurable (ae_lt_top (hmA hFn) hin), hcA hFp, hcA hFn, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.D_pos.le]
  have hden : R.markedIntegral Finset.univ V =
      R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
        ∫ η, chartDensity (configSetting (coldCaseGround R V) (coldCaseGround R V).allVacant) η := by
    rw [hC.marked, partitionFunction_univ _ hC.gas.weight.measurable_weightDensity, weightDensity_eq hC.gas ha,
      hC.gas.mass _ ha, ENNReal.toReal_ofReal (integral_nonneg (chartDensity_nonneg _))]
  unfold fullyMarkedExpectation weightedMean
  rw [hnum, hden, integral_parts hC.gas H ha hI, ← mul_sub, mul_div_mul_left _ _ hC.D_pos.ne']
end ColdFacts
section Spins
open ProbabilityTheory
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  {A : PairConstraint S} {m : ∀ i, Measure (S i)} {Gw : (∀ i, S i) → ℝ} {zz : I → ℝ}
private theorem isAdmissible_update_vacant {σ : ∀ i, S i} {i : I} {s : S i}
    (hσ : A.IsAdmissible (Function.update σ i s)) : A.IsAdmissible (Function.update σ i (A.vacant i)) := by apply _root_.YangMills.Construction.Dobrushin.isAdmissible_update_vacant_of_isAdmissible_update <;> assumption
private theorem weightDensity_of_not_admissible {σ : ∀ i, S i} (hσ : ¬ A.IsAdmissible σ) :
    A.weightDensity Gw σ = 0 := if_neg hσ
private theorem lintegral_single_spin_le [∀ i, SigmaFinite (m i)] (h : A.IsActivityBounded m Gw zz) (i : I)
    (g : S i → ℝ≥0∞) (hg : Measurable g) (hg0 : g (A.vacant i) = 0) (c : ℝ≥0∞)
    (hpaid : ∀ x, A.IsAdmissible x →
      ∫⁻ v in {A.vacant i}ᶜ, g v * A.weightDensity Gw (Function.update x i v) ∂m i ≤
        c * A.weightDensity Gw (Function.update x i (A.vacant i))) :
    ∫⁻ σ, g (σ i) * A.weightDensity Gw σ ∂Measure.pi m ≤ c * ∫⁻ σ, A.weightDensity Gw σ ∂Measure.pi m := by
  classical
  have hd := h.measurable_weightDensity
  have hf : Measurable fun σ : ∀ i, S i => g (σ i) * A.weightDensity Gw σ :=
    (hg.comp (measurable_pi_apply i)).mul hd
  have hf2 : Measurable fun σ : ∀ i, S i => c * A.weightDensity Gw σ := hd.const_mul c
  have hi : i ∉ Finset.univ.erase i := Finset.notMem_erase i _
  have hu : insert i (Finset.univ.erase i) = Finset.univ := Finset.insert_erase (Finset.mem_univ i)
  have key : ∀ f : (∀ i, S i) → ℝ≥0∞, Measurable f → ∫⁻ σ, f σ ∂Measure.pi m =
      (∫⋯∫⁻_Finset.univ.erase i, (fun x => ∫⁻ v, f (Function.update x i v) ∂m i) ∂m) A.vacant := by
    intro f hf
    have e := lmarginal_insert' (μ := m) f hf hi
    rw [hu] at e
    rw [lintegral_eq_lmarginal_univ A.vacant, e]
  rw [← lintegral_const_mul _ hd, key _ hf, key _ hf2]
  refine lmarginal_mono (fun x => ?_) _
  show ∫⁻ v, g (Function.update x i v i) * A.weightDensity Gw (Function.update x i v) ∂m i ≤
    ∫⁻ v, c * A.weightDensity Gw (Function.update x i v) ∂m i
  simp only [Function.update_self]
  have hm1 : Measurable fun v => A.weightDensity Gw (Function.update x i v) := hd.comp (measurable_update x)
  have hs : MeasurableSet ({A.vacant i}ᶜ : Set (S i)) := (h.measurableSet_vacant i).compl
  have e1 : ∫⁻ v, g v * A.weightDensity Gw (Function.update x i v) ∂m i =
      ∫⁻ v in {A.vacant i}ᶜ, g v * A.weightDensity Gw (Function.update x i v) ∂m i := by
    rw [← lintegral_indicator hs]
    refine lintegral_congr fun v => ?_
    by_cases hv : v = A.vacant i
    · subst hv
      simp [hg0]
    · rw [Set.indicator_of_mem (show v ∈ ({A.vacant i}ᶜ : Set (S i)) from hv)]
  have e2 : A.weightDensity Gw (Function.update x i (A.vacant i)) ≤
      ∫⁻ v, A.weightDensity Gw (Function.update x i v) ∂m i := by
    have e3 : ∫⁻ v in {A.vacant i}, A.weightDensity Gw (Function.update x i v) ∂m i =
        A.weightDensity Gw (Function.update x i (A.vacant i)) := by
      rw [setLIntegral_congr_fun (g := fun _ => A.weightDensity Gw (Function.update x i (A.vacant i)))
        (h.measurableSet_vacant i) (fun v hv => by rw [Set.mem_singleton_iff.mp hv]), setLIntegral_const,
        h.measure_vacant i, mul_one]
    exact e3 ▸ setLIntegral_le_lintegral _ _
  rw [e1, lintegral_const_mul _ hm1]
  by_cases hx : A.IsAdmissible (Function.update x i (A.vacant i))
  · have := hpaid _ hx
    simp only [Function.update_idem] at this
    exact this.trans (by gcongr)
  · have hz : ∀ v, A.weightDensity Gw (Function.update x i v) = 0 := fun v =>
      weightDensity_of_not_admissible fun ha => hx (isAdmissible_update_vacant ha)
    simp [hz]
abbrev _root_.YangMills.SharedProofs.p71899 := @lintegral_single_spin_le
end Spins
section Scores
private def occupiedScore (A : ResponseSetup R) {G : GasGround R n} (i : G.GasSpin) : G.SpinValue i → ℝ≥0∞ :=
  Sum.elim (fun _ => 0) fun v => ENNReal.ofReal (Real.exp (_root_.YangMills.Construction.WeightedResponses.spinScore A i (Sum.inr v)))
private theorem measurable_occupiedScore (A : ResponseSetup R) (hs : Measurable A.score) {G : GasGround R n}
    (i : G.GasSpin) : Measurable (occupiedScore A i) := by
  refine measurable_const.sumElim ?_
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  show Measurable fun v : G.SpinState i => ∑ z : i.1.2, A.score (v.1.2.1 z)
  refine Finset.measurable_sum _ fun z _ => hs.comp ?_
  exact (measurable_pi_apply z).comp (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe))
abbrev _root_.YangMills.DeltaSharedProofs.p501890 := @measurable_occupiedScore
private theorem labelAt_of_mem_sites (G : GasGround R n) (σ : G.Config) {y : TorusSite (n * R.params.side)}
    (h : y ∈ (G.familyOf σ).sites) :
    ∃ (i : G.GasSpin) (v : G.SpinState i) (hz : y ∈ i.1.2), σ i = Sum.inr v ∧
      (G.familyOf σ).labelAt h = v.1.2.1 ⟨y, hz⟩ := by
  classical
  have key : ∀ (θ : GasSupport R n) (hH : (G.familyOf σ).Occupies θ) (hz : y ∈ θ.2),
      ∃ (i : G.GasSpin) (v : G.SpinState i) (hz' : y ∈ i.1.2), σ i = Sum.inr v ∧
        ((G.familyOf σ).state hH).2.1 ⟨y, hz⟩ = v.1.2.1 ⟨y, hz'⟩ := by
    intro θ hH hz
    by_cases hS : G.IsGasSupport θ
    · rcases hv : σ ⟨θ, hS⟩ with u | v
      · exfalso
        have e : G.familyOf σ θ = Sum.inl () := by
          unfold GasGround.familyOf
          rw [dif_pos hS, hv]
        unfold GasFamily.Occupies at hH
        rw [e] at hH
        simp at hH
      · refine ⟨⟨θ, hS⟩, v, hz, hv, ?_⟩
        have e : G.familyOf σ θ = Sum.inr v.1 := by
          unfold GasGround.familyOf
          rw [dif_pos hS, hv]
        unfold GasFamily.state
        simp only [e]
        rfl
    · exfalso
      have e : G.familyOf σ θ = Sum.inl () := by
        unfold GasGround.familyOf
        rw [dif_neg hS]
      unfold GasFamily.Occupies at hH
      rw [e] at hH
      simp at hH
  exact key _ (GasFamily.exists_of_mem_sites h).choose_spec.1 (GasFamily.exists_of_mem_sites h).choose_spec.2
abbrev _root_.YangMills.SharedProofs.p29352 := @labelAt_of_mem_sites
open Classical in
private def spinsAt (G : GasGround R n) (y : TorusSite (n * R.params.side)) : Finset G.GasSpin :=
  Finset.univ.filter fun i => y ∈ i.1.2
private theorem chartSiteScore_le (A : ResponseSetup R) (hnn : ∀ w, 0 ≤ A.score w) (G : GasGround R n)
    (hst : G.recordedSites = ∅) (σ : G.Config) (y : TorusSite (n * R.params.side)) :
    ENNReal.ofReal (chartSiteScore A (configSetting G σ) y) ≤ ∑ i ∈ spinsAt G y, occupiedScore A i (σ i) := by
  classical
  unfold chartSiteScore siteScore
  by_cases hy : y ∈ (configSetting G σ).support
  · rw [dif_pos hy]
    have hs : y ∈ (G.familyOf σ).sites := by
      have h1 : y ∈ G.recordedSites ∪ (G.familyOf σ).sites := hy
      rw [hst] at h1
      simpa using h1
    have e1 : (configSetting G σ).labelling ⟨y, hy⟩ = (G.familyOf σ).labelAt hs := dif_pos hs
    obtain ⟨i, v, hz, hv, e2⟩ := labelAt_of_mem_sites G σ hs
    rw [e1, e2]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => occupiedScore A i (σ i)) (fun _ _ => zero_le)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hz⟩))
    show _ ≤ occupiedScore A i (σ i)
    rw [hv]
    show _ ≤ ENNReal.ofReal (Real.exp (∑ z : i.1.2, A.score (v.1.2.1 z)))
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : A.score (v.1.2.1 ⟨y, hz⟩) ≤ ∑ z : i.1.2, A.score (v.1.2.1 z) :=
      Finset.single_le_sum (f := fun z => A.score (v.1.2.1 z)) (fun _ _ => hnn _) (Finset.mem_univ _)
    have h2 := Real.add_one_le_exp (∑ z : i.1.2, A.score (v.1.2.1 z))
    linarith
  · rw [dif_neg hy]
    simp
private theorem sum_spinActivity_le_one (G : GasGround R n) (y : TorusSite (n * R.params.side)) {c rt : ℝ}
    (hrt : 0 < rt) (hc : 0 ≤ c * R.coupling)
    (hcount : ∑ θ ∈ supportsAtBlock R.params.side R.range (parentBlock R.params.side y),
        clusterWeight R.params.side c R.coupling R.range θ *
          ((supportCore R.params.side R.range θ).card : ℝ) ^ 4 *
          Real.exp (2 * rt * (siteDiameter (supportCore R.params.side R.range θ) : ℝ)) ≤
      Real.exp (-(8 * c * R.coupling))) :
    ∑ i ∈ spinsAt G y, G.spinActivity c i ≤ 1 := by
  classical
  have hw : ∀ θ : GasSupport R n, 0 < clusterWeight R.params.side c R.coupling R.range θ :=
    fun θ => Real.exp_pos _
  have hcore : ∀ i ∈ spinsAt G y, parentBlock R.params.side y ∈ supportCore R.params.side R.range i.1 := by
    intro i hi
    have hy := (Finset.mem_filter.mp hi).2
    have hy' : y ∈ clusterSupportSites R.params.side i.1 := Finset.mem_union_right _ hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨y, Finset.mem_inter.mpr ⟨by simp [sitesInBlocks],
      (mem_thickening _ _ _).2 ⟨y, hy', by rw [supDist_self]; omega⟩⟩⟩⟩
  have hsub : (spinsAt G y).image Subtype.val ⊆
      supportsAtBlock R.params.side R.range (parentBlock R.params.side y) := by
    intro θ hθ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hθ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2.isCluster, hcore i hi⟩
  have hle : ∀ θ ∈ (spinsAt G y).image Subtype.val, clusterWeight R.params.side c R.coupling R.range θ ≤
      clusterWeight R.params.side c R.coupling R.range θ * ((supportCore R.params.side R.range θ).card : ℝ) ^ 4 *
        Real.exp (2 * rt * (siteDiameter (supportCore R.params.side R.range θ) : ℝ)) := by
    intro θ hθ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hθ
    have h1 : (1 : ℝ) ≤ ((supportCore R.params.side R.range i.1).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨_, hcore i hi⟩
    have h2 : (1 : ℝ) ≤ ((supportCore R.params.side R.range i.1).card : ℝ) ^ 4 := one_le_pow₀ h1
    have h3 : (1 : ℝ) ≤ Real.exp (2 * rt * (siteDiameter (supportCore R.params.side R.range i.1) : ℝ)) :=
      Real.one_le_exp (by positivity)
    have h4 := hw i.1
    calc clusterWeight R.params.side c R.coupling R.range i.1 =
          clusterWeight R.params.side c R.coupling R.range i.1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  calc ∑ i ∈ spinsAt G y, G.spinActivity c i =
        ∑ θ ∈ (spinsAt G y).image Subtype.val, clusterWeight R.params.side c R.coupling R.range θ :=
        (Finset.sum_image fun a _ b _ h => Subtype.ext h).symm
    _ ≤ ∑ θ ∈ (spinsAt G y).image Subtype.val, clusterWeight R.params.side c R.coupling R.range θ *
          ((supportCore R.params.side R.range θ).card : ℝ) ^ 4 *
          Real.exp (2 * rt * (siteDiameter (supportCore R.params.side R.range θ) : ℝ)) :=
        Finset.sum_le_sum hle
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun θ _ _ => by
        have := hw θ
        positivity
    _ ≤ _ := hcount
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
private theorem lintegral_occupiedScore_le {V : TorusField n} {c : ℝ}
    (hC : ColdFacts R V ((coldCaseGround R V).spinActivity c)) (A : ResponseSetup R)
    (hsb : Measurable A.score) (y : TorusSite (n * R.params.side))
    (hpaid : ∀ (i : (coldCaseGround R V).GasSpin) (σ : (coldCaseGround R V).Config),
      (coldCaseGround R V).pairConstraint.IsAdmissible σ →
      ∫⁻ v in {(coldCaseGround R V).pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (_root_.YangMills.Construction.WeightedResponses.spinScore A i v)) *
          (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight (Function.update σ i v)
            ∂((coldCaseGround R V).referenceMeasure ∅ i) ≤
        ENNReal.ofReal ((coldCaseGround R V).spinActivity c i) *
          (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight
            (Function.update σ i ((coldCaseGround R V).pairConstraint.vacant i)))
    (hsum : ∑ i ∈ spinsAt (coldCaseGround R V) y, (coldCaseGround R V).spinActivity c i ≤ 1) :
    ∫⁻ σ, (∑ i ∈ spinsAt (coldCaseGround R V) y, occupiedScore A i (σ i)) *
      (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ
        ∂Measure.pi ((coldCaseGround R V).referenceMeasure ∅) ≤
      (coldCaseGround R V).partitionFunction ∅ := by
  have hw := hC.gas.weight
  have hd := hw.measurable_weightDensity
  have hspin : ∀ i : (coldCaseGround R V).GasSpin, ∫⁻ σ, occupiedScore A i (σ i) *
      (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ
        ∂Measure.pi ((coldCaseGround R V).referenceMeasure ∅) ≤
      ENNReal.ofReal ((coldCaseGround R V).spinActivity c i) * (coldCaseGround R V).partitionFunction ∅ := by
    intro i
    refine lintegral_single_spin_le hw i _ (measurable_occupiedScore A hsb i) rfl _ fun x hx' => ?_
    refine le_trans (le_of_eq ?_) (hpaid i x hx')
    refine setLIntegral_congr_fun (hw.measurableSet_vacant i).compl fun v hv => ?_
    rcases v with u | v
    · exact absurd (by rfl) hv
    · rfl
  have hz : ∀ i, 0 ≤ (coldCaseGround R V).spinActivity c i := fun i => (Real.exp_pos _).le
  simp only [Finset.sum_mul]
  rw [lintegral_finsetSum _ (f := fun (i : (coldCaseGround R V).GasSpin) (σ : (coldCaseGround R V).Config) =>
    occupiedScore A i (σ i) * (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ)
    fun i _ => ((measurable_occupiedScore A hsb i).comp (measurable_pi_apply i)).mul hd]
  calc _ ≤ ∑ i ∈ spinsAt (coldCaseGround R V) y, ENNReal.ofReal ((coldCaseGround R V).spinActivity c i) *
          (coldCaseGround R V).partitionFunction ∅ :=
        Finset.sum_le_sum fun i _ => hspin i
    _ = ENNReal.ofReal (∑ i ∈ spinsAt (coldCaseGround R V) y, (coldCaseGround R V).spinActivity c i) *
          (coldCaseGround R V).partitionFunction ∅ := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ => hz i]
    _ ≤ 1 * (coldCaseGround R V).partitionFunction ∅ := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hsum
    _ = _ := one_mul _
end Scores
section Response
variable {V : TorusField n} {z : (coldCaseGround R V).GasSpin → ℝ}
private theorem isCaseReal_liveCenteredResponse (hC : ColdFacts R V z) {A : ResponseSetup R}
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold
      A.hull A.siteRemainder A.totalRemainder) (y : TorusSite (n * R.params.side))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) :
    IsCaseReal (lift (fun Yt _ p => liveCenteredResponse A y h Yt p) : CaseFunction R n) := by
  classical
  have hrow := hC.base.row
  have hfit := hC.base.fits
  have hbs := hC.side
  refine ⟨fun Yt bad b => ?_, ?_⟩
  · have hq := hA.hull_borel (n * R.params.side) hbs y Yt h
    have hD := (hrow.2.borel (n * R.params.side) hbs Yt).1
    have hlive : MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
        IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
      have e : {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
          IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} =
          (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
            if IsHullState R.params (clusterRange R.coupling) p.1 Yt then
              R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0) ⁻¹' Set.Ioi 0 := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]
        constructor
        · intro hl
          rw [if_pos hl.1]
          exact hl.2
        · intro hl
          by_cases hh : IsHullState R.params (clusterRange R.coupling) p.1 Yt
          · rw [if_pos hh] at hl
            exact ⟨hh, hl⟩
          · rw [if_neg hh] at hl
            exact absurd hl (lt_irrefl _)
      rw [e]
      exact hD measurableSet_Ioi
    have e : (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        lift (fun Yt _ p => liveCenteredResponse A y h Yt p) p.1 Yt p.2 bad b) =
        fun p => if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
          (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
            A.hull (n * R.params.side) y p.1 Yt p.2 h else 0) -
            A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h else 0 := by
      funext p
      show liveCenteredResponse A y h Yt (p.1, p.2) = _
      unfold liveCenteredResponse centeredHullResponse
      by_cases hl : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
      · simp only [if_pos hl]
      · simp only [if_neg hl]
    rw [e]
    exact Measurable.ite hlive (hq.sub_const _) measurable_const
  · intro W Yt ωt bad b u hl _ _
    have hh : IsHullState R.params (clusterRange R.coupling) (TorusFields.gaugeTransform u W) Yt :=
      (isHullState_gaugeTransform hfit u W _ Yt).mpr hl.1
    have hl' : IsLiveState R.params R.coupling R.labelWeight (TorusFields.gaugeTransform u W) Yt
        (R.labels.act Yt u ωt) :=
      ⟨hh, by rw [hrow.2.gauge (n * R.params.side) hbs W Yt ωt u hl.1]; exact hl.2⟩
    show liveCenteredResponse A y h Yt (TorusFields.gaugeTransform u W, R.labels.act Yt u ωt) =
      liveCenteredResponse A y h Yt (W, ωt)
    unfold liveCenteredResponse
    dsimp only
    rw [if_pos hl', if_pos hl]
    unfold centeredHullResponse
    rw [hA.hull_gauge (n * R.params.side) hbs y u W Yt ωt hl h]
private theorem isCaseReal_bondScore (hC : ColdFacts R V z) (hsb : BondScoreProperties) (c : TorusBond n) :
    IsCaseReal (lift (fun _ b p => bondScore R.params R.coupling p.1 V b c) : CaseFunction R n) := by
  refine ⟨fun Yt bad b => ?_, ?_⟩
  · have h1 := (hsb R.params hC.base.fits R.coupling n b c).2.2.2.2
    have h2 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => (p.1, V) :=
      measurable_fst.prodMk measurable_const
    have h3 := h1.comp h2
    simp only [lift]
    exact h3
  · intro W Yt ωt bad b u _ h1 _
    simp only [lift]
    exact bondScore_gaugeTransform W V h1 c
private theorem measurable_inSetting {H : CaseFunction R n} (hH : IsCaseReal H) (G : GasGround R n)
    (σ : G.Config) : Measurable (inSetting G H σ) :=
  (hH.borel _ _ _).comp ((YangMills.Construction.ClusterExpansionOfAStep.ChartSetting.measurable_field _).prodMk
    measurable_const)
private theorem inSetting_lift (G : GasGround R n) (f : ColdFunction R n) (σ : G.Config)
    (η : FreeCoords (configSetting G σ).free) : inSetting G (lift f) σ η =
      f (configSetting G σ).support (configSetting G σ).bases
        ((configSetting G σ).field η, (configSetting G σ).labelling) := rfl
private theorem configSetting_coarse (G : GasGround R n) (σ : G.Config) :
    (configSetting G σ).coarse = G.coarse := rfl
private theorem abs_liveCenteredResponse_le {A : ResponseSetup R}
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold
      A.hull A.siteRemainder A.totalRemainder) (hbs : IsBlockTorusSide R.params (n * R.params.side))
    (hC₀ : 0 ≤ A.responseParams.C₀) (hsn : ∀ w, 0 ≤ A.score w) (y : TorusSite (n * R.params.side))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) :
    |liveCenteredResponse A y h Yt (W, ωt)| ≤
      (A.responseParams.C₀ + siteScore A.score Yt ωt y) * weightNorm R.params.side R.depth h := by
  classical
  unfold liveCenteredResponse
  dsimp only
  split_ifs with hl
  · exact hA.size_hull (n * R.params.side) hbs y W Yt ωt hl h
  · rw [abs_zero]
    exact mul_nonneg (add_nonneg hC₀ (siteScore_nonneg hsn _ _ _)) (weightNorm_nonneg _ _ _)
private theorem ofReal_affine_le {s sz C : ℝ} {b : ℝ≥0∞} (hsz : 0 ≤ sz) (hb : ENNReal.ofReal s ≤ b) :
    ENNReal.ofReal ((C + s) * sz) ≤ ENNReal.ofReal (C * sz) + ENNReal.ofReal sz * b := by
  have e : (C + s) * sz = C * sz + s * sz := by ring
  rw [e]
  refine ENNReal.ofReal_add_le.trans ?_
  gcongr
  rw [mul_comm, ENNReal.ofReal_mul hsz]
  gcongr
private theorem response_properties (hC : ColdFacts R V z) {A : ResponseSetup R}
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold
      A.hull A.siteRemainder A.totalRemainder) (hC₀ : 0 ≤ A.responseParams.C₀) (hsn : ∀ w, 0 ≤ A.score w)
    (y : TorusSite (n * R.params.side)) (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
    {Bs : (coldCaseGround R V).Config → ℝ≥0∞} (hBm : Measurable Bs)
    (hBle : ∀ σ, ENNReal.ofReal (chartSiteScore A (configSetting (coldCaseGround R V) σ) y) ≤ Bs σ)
    (hBZ : ∫⁻ σ, Bs σ * (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ
      ∂Measure.pi ((coldCaseGround R V).referenceMeasure ∅) ≤ (coldCaseGround R V).partitionFunction ∅) :
    (∀ Yt b, Integrable (coldIntegrand R V (fun Yt _ p => liveCenteredResponse A y h Yt p) Yt b)
      (fieldLabelMeasure R n Yt)) ∧
    coldWeightedIntegral R V (fun Yt _ p => |liveCenteredResponse A y h Yt p|) ≤
      (A.responseParams.C₀ + 1) * weightNorm R.params.side R.depth h *
        coldWeightedIntegral R V (fun _ _ _ => 1) ∧
    gasResponseShift A (coldCaseGround R V) y h =
      coldExpectation R V (fun Yt _ p => liveCenteredResponse A y h Yt p) -
        fullyMarkedExpectation R V (fun W => liveCenteredResponse A y h ∅ (W, emptyLabeling R)) := by
  classical
  have hH := isCaseReal_liveCenteredResponse hC hA y h
  have hf := hC.gas
  have hd := hf.weight.measurable_weightDensity
  have hsz : 0 ≤ weightNorm R.params.side R.depth h := weightNorm_nonneg _ _ _
  have hc0 : 0 ≤ (A.responseParams.C₀ + 1) * weightNorm R.params.side R.depth h := mul_nonneg (by linarith) hsz
  have hcut : ∀ (σ : (coldCaseGround R V).Config) η,
      |inSetting (coldCaseGround R V) (lift (fun Yt _ p => liveCenteredResponse A y h Yt p)) σ η| ≤
        (A.responseParams.C₀ + chartSiteScore A (configSetting (coldCaseGround R V) σ) y) *
          weightNorm R.params.side R.depth h :=
    fun σ η => abs_liveCenteredResponse_le hA hC.side hC₀ hsn y h _ _ _
  have hZ := (total_facts hf).2
  have hgas : (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|)
      (lift (fun Yt _ p => liveCenteredResponse A y h Yt p))) ≤
      ENNReal.ofReal ((A.responseParams.C₀ + 1) * weightNorm R.params.side R.depth h) *
        (coldCaseGround R V).partitionFunction ∅ := by
    refine (gasMass_le hf (B := fun σ => ENNReal.ofReal (A.responseParams.C₀ * weightNorm R.params.side R.depth h) +
      ENNReal.ofReal (weightNorm R.params.side R.depth h) * Bs σ) fun σ η _ => ?_).trans ?_
    · exact (ENNReal.ofReal_le_ofReal (hcut σ η)).trans (ofReal_affine_le hsz (hBle σ))
    · have e : ∀ σ, (ENNReal.ofReal (A.responseParams.C₀ * weightNorm R.params.side R.depth h) +
          ENNReal.ofReal (weightNorm R.params.side R.depth h) * Bs σ) *
          (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ =
          ENNReal.ofReal (A.responseParams.C₀ * weightNorm R.params.side R.depth h) *
            (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ +
            ENNReal.ofReal (weightNorm R.params.side R.depth h) *
              (Bs σ * (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ) := by
        intro σ
        rw [add_mul, mul_assoc]
      simp only [e]
      rw [lintegral_add_left (hd.const_mul _), lintegral_const_mul _ hd,
        lintegral_const_mul _ (show Measurable fun σ =>
          Bs σ * (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ
          from hBm.mul hd)]
      have e2 : ENNReal.ofReal ((A.responseParams.C₀ + 1) * weightNorm R.params.side R.depth h) =
          ENNReal.ofReal (A.responseParams.C₀ * weightNorm R.params.side R.depth h) +
            ENNReal.ofReal (weightNorm R.params.side R.depth h) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hC₀ hsz) hsz]
        congr 1
        ring
      rw [e2, add_mul]
      exact add_le_add le_rfl (mul_le_mul' le_rfl hBZ)
  have hfin : (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|)
      (lift (fun Yt _ p => liveCenteredResponse A y h Yt p))) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZ) hgas
  obtain ⟨hInt, hmean⟩ := coldExpectation_lift hC hH hfin
  refine ⟨hInt, ?_, ?_⟩
  · have hm1 : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
        Measurable ((fun Yt _ p => |liveCenteredResponse A y h Yt p| : ColdFunction R n) Yt b) := fun Yt b =>
      continuous_abs.measurable.comp (hH.borel Yt ∅ b)
    have hcm := coldMass_eq hC (f := fun Yt _ p => liveCenteredResponse A y h Yt p) (fun Yt b => hH.borel Yt ∅ b)
      measurable_absPart
    have hne := coldMass_ne_top hC hH hfin
    have hfin1 : coldMass R V (fun Yt b p =>
        ENNReal.ofReal |(fun Yt _ p => |liveCenteredResponse A y h Yt p| : ColdFunction R n) Yt b p|) ≠ ⊤ := by
      have e : (fun (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
          (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) =>
          ENNReal.ofReal |(fun Yt _ p => |liveCenteredResponse A y h Yt p| : ColdFunction R n) Yt b p|) =
          fun Yt _ p => ENNReal.ofReal |liveCenteredResponse A y h Yt p| := by
        funext Yt b p
        simp only [abs_abs]
      rw [e]
      exact hne
    rw [coldWeightedIntegral_eq hC.base hC.side V hC.weights hm1 hfin1]
    have h1 : (coldMass R V fun Yt b p =>
        ENNReal.ofReal ((fun Yt _ p => |liveCenteredResponse A y h Yt p| : ColdFunction R n) Yt b p)) =
        ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
          (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|)
            (lift (fun Yt _ p => liveCenteredResponse A y h Yt p))) :=
      hcm.symm.trans (hC.image _ _ (isCaseFunctional_weightBy hH measurable_absPart))
    have h2 : coldWeightedIntegral R V (fun _ _ _ => 1) =
        (ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
          (coldCaseGround R V).partitionFunction ∅).toReal := by
      rw [coldWeightedIntegral_one hC]
      have h4 := coarseStateWeight_eq (coldCaseGround R V)
      rw [hC.image _ _ (isCaseFunctional_weightBy isCaseReal_one measurable_posPart), gasMass_one hC.gas] at h4
      exact h4
    rw [h1, h2]
    have h3 : (ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
        (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|)
          (lift (fun Yt _ p => liveCenteredResponse A y h Yt p)))).toReal ≤
        (ENNReal.ofReal ((A.responseParams.C₀ + 1) * weightNorm R.params.side R.depth h) *
          (ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
            (coldCaseGround R V).partitionFunction ∅)).toReal := by
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZ)) ?_
      rw [mul_left_comm]
      gcongr
    rw [ENNReal.toReal_mul (a := ENNReal.ofReal ((A.responseParams.C₀ + 1) * weightNorm R.params.side R.depth h)),
      ENNReal.toReal_ofReal hc0] at h3
    have h5 : 0 ≤ (coldMass R V fun Yt b p =>
        ENNReal.ofReal (-(fun Yt _ p => |liveCenteredResponse A y h Yt p| : ColdFunction R n) Yt b p)).toReal :=
      ENNReal.toReal_nonneg
    linarith
  · have ha := isAdmissible_allVacant (coldCaseGround R V)
    have e1 : (coldCaseGround R V).expectation ∅
        (fun σ => chartResponse A (configSetting (coldCaseGround R V) σ) y h) =
        gasExpectationOfCase (coldCaseGround R V) (lift (fun Yt _ p => liveCenteredResponse A y h Yt p)) := by
      unfold gasExpectationOfCase GasGround.expectation
      refine integral_congr_ae ?_
      filter_upwards [ae_admissible hf] with σ hσ
      unfold chartResponse
      refine weightedMean_congr' fun η hη => ?_
      have hl := chartSetting_live hC.base.row hC.base.fits hC.floor (hf.setting σ hσ)
        (inBalls_of_chartDensity _ hη)
      show _ = liveCenteredResponse A y h _ (_, _)
      unfold liveCenteredResponse
      dsimp only
      rw [if_pos hl]
    have hI : Integrable fun η => inSetting (coldCaseGround R V)
        (lift (fun Yt _ p => liveCenteredResponse A y h Yt p)) (coldCaseGround R V).allVacant η *
          chartDensity (configSetting (coldCaseGround R V) (coldCaseGround R V).allVacant) η :=
      integrable_mul_of_bound (hf.density_int _ ha) (chartDensity_nonneg _) (measurable_inSetting hH _ _)
        fun η _ => hcut _ η
    have e2 : chartResponse A (coldCaseGround R V).groundSetting y h =
        fullyMarkedExpectation R V (fun W => liveCenteredResponse A y h ∅ (W, emptyLabeling R)) := by
      rw [← configSetting_allVacant, fullyMarkedExpectation_eq hC hH
        (g := fun W => liveCenteredResponse A y h ∅ (W, emptyLabeling R)) (fun W b _ _ => rfl) hI]
      unfold chartResponse
      refine weightedMean_congr' fun η hη => ?_
      have hl := chartSetting_live hC.base.row hC.base.fits hC.floor (hf.setting _ ha)
        (inBalls_of_chartDensity _ hη)
      show _ = liveCenteredResponse A y h _ (_, _)
      unfold liveCenteredResponse
      dsimp only
      rw [if_pos hl]
    unfold gasResponseShift
    rw [e1, e2, hmean]
private theorem score_conditions (hC : ColdFacts R V z) (hsb : BondScoreProperties) (c : TorusBond n) :
    (∀ Yt b, Integrable (coldIntegrand R V (fun _ b p => bondScore R.params R.coupling p.1 V b c) Yt b)
      (fieldLabelMeasure R n Yt)) ∧
    gasBondScoreShift (coldCaseGround R V) c =
      coldExpectation R V (fun _ b p => bondScore R.params R.coupling p.1 V b c) -
        fullyMarkedExpectation R V (fun W => bondScore R.params R.coupling W V (centreBases R.params.side n) c) := by
  classical
  have hH := isCaseReal_bondScore hC hsb c
  have hf := hC.gas
  have hbound : ∀ (σ : (coldCaseGround R V).Config) η,
      |inSetting (coldCaseGround R V) (lift (fun _ b p => bondScore R.params R.coupling p.1 V b c)) σ η| ≤ 2 :=
    fun σ η => by
      simp only [inSetting_lift]
      exact (hsb R.params hC.base.fits R.coupling n _ c).2.2.1 _ _
  have hfin : (coldCaseGround R V).gasMass ∅ (weightBy (fun u => ENNReal.ofReal |u|)
      (lift (fun _ b p => bondScore R.params R.coupling p.1 V b c))) ≠ ⊤ :=
    ne_top_of_le_ne_top (gas_const_ne_top hC (c := ENNReal.ofReal 2) ENNReal.ofReal_ne_top)
      (gasMass_le hf fun σ η _ => ENNReal.ofReal_le_ofReal (hbound σ η))
  obtain ⟨hInt, hmean⟩ := coldExpectation_lift hC hH hfin
  refine ⟨hInt, ?_⟩
  have ha := isAdmissible_allVacant (coldCaseGround R V)
  have hI : Integrable fun η => inSetting (coldCaseGround R V)
      (lift (fun _ b p => bondScore R.params R.coupling p.1 V b c)) (coldCaseGround R V).allVacant η *
        chartDensity (configSetting (coldCaseGround R V) (coldCaseGround R V).allVacant) η :=
    integrable_mul_of_bound (hf.density_int _ ha) (chartDensity_nonneg _) (measurable_inSetting hH _ _)
      fun η _ => hbound _ η
  have hs : ∀ (σ : (coldCaseGround R V).Config), chartBondScore (configSetting (coldCaseGround R V) σ) c =
      weightedMean (chartDensity (configSetting (coldCaseGround R V) σ))
        (inSetting (coldCaseGround R V) (lift (fun _ b p => bondScore R.params R.coupling p.1 V b c)) σ) :=
    fun σ => by
      unfold chartBondScore
      refine weightedMean_congr' fun η _ => ?_
      simp only [inSetting_lift]
      rw [configSetting_coarse]
      rfl
  have e1 : (coldCaseGround R V).expectation ∅ (fun σ => chartBondScore (configSetting (coldCaseGround R V) σ) c) =
      gasExpectationOfCase (coldCaseGround R V) (lift (fun _ b p => bondScore R.params R.coupling p.1 V b c)) := by
    simp only [hs]
    rfl
  have e2 : chartBondScore (coldCaseGround R V).groundSetting c =
      fullyMarkedExpectation R V (fun W => bondScore R.params R.coupling W V (centreBases R.params.side n) c) := by
    rw [← configSetting_allVacant, fullyMarkedExpectation_eq hC hH
      (g := fun W => bondScore R.params R.coupling W V (centreBases R.params.side n) c)
      (fun W b hh hb => by
        rw [← eq_centreBases_of_baseLaw hC.base.fits hh hb]
        simp only [lift]) hI]
    exact hs _
  unfold gasBondScoreShift
  rw [e1, e2, hmean]
end Response
private def withEqualCouplings (R : StepSetup) : StepSetup := { R with nextCoupling := R.coupling }
private theorem gasRate_pos (T : ParameterAssignment) (hT : T.Admissible) : 0 < T.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
end ColdShiftLemmas
set_option maxHeartbeats 1000000 in
open ColdShiftLemmas in
theorem gasShiftsAreColdExpectations_holds (hM : caseMeanEqGasMeanStatement) (hP : clusterScoreIntegralBound)
    (hB : gasIntegrandMeasurableStatement) (hI : CaseMassEqGasMass)
    (hCf : GasConfigIsAdmissibleSetting) (hW : GasIsActivityBounded) (hMs : SettingMassEqIntegral)
    (hCL : ActivityConditionalLawsStatement) (hBo : CaseIntegrandMeasurable) (hK : BondKernelProperties)
    (hsb : BondScoreProperties) (hMG : MarkedIntegralEqPartitionOfCouplingLe)
    (hCC : _root_.YangMills.Construction.ClusterBounds.ClusterSumBound) (hWB : ConfigurationWeightMeasurable)
    (hf1 : CouplingFloorExists) : GasShiftsAreColdExpectations := by
  classical
  obtain ⟨r₁, p₁, g₁⟩ := hM
  obtain ⟨r₂, p₂, g₂⟩ := hP
  obtain ⟨r₃, p₃, g₃⟩ := hW
  obtain ⟨r₄, p₄, g₄⟩ := hMs
  obtain ⟨r₅, p₅, g₅⟩ := hMG
  refine ⟨fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (min (r₄ c) (r₅ c))),
    fun c => lt_min (lt_min (p₁ c) (p₂ c)) (lt_min (p₃ c) (lt_min (p₄ c) (p₅ c))), fun T hD hrt K => ?_⟩
  obtain ⟨y₁, G₁⟩ := g₁ T hD (hrt.trans ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨y₂, G₂⟩ := g₂ T hD (hrt.trans ((min_le_left _ _).trans (min_le_right _ _))) K
  obtain ⟨y₃, G₃⟩ := g₃ T hD (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₄, G₄⟩ := g₄ T hD (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  obtain ⟨y₅, G₅⟩ := g₅ T hD (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨y₆, G₆⟩ := hB T hD
  obtain ⟨y₇, G₇⟩ := hI T hD
  obtain ⟨y₈, G₈⟩ := hCf T hD
  obtain ⟨y₉, G₉⟩ := hBo T hD
  obtain ⟨y₁₀, G₁₀⟩ := hCC T hD
  obtain ⟨y₁₁, G₁₁⟩ := hf1 1 (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 16) T.rt one_pos
  refine ⟨max 1 (max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (max y₈ (max y₉ (max y₁₀ (max y₁₁
    (max T.floorMin (200 * T.B))))))))))))), fun y hy R A hKA hAt hArr n _ hn V hV => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁, b₁₂, b₁₃⟩ := hy
  have hR := hAt.onFamily
  have hxc := hR.le_coupling
  have hx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    linarith
  have hfit : R.params.Admissible := hR.params_eq ▸ hD.fits y b₁₂
  have hrow : R.HasExpansions := hR.isStep.1
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have en₀ : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have eσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hnT : T.n₀ ≤ n := en₀ ▸ hn
  have hVT : IsCold (9 / 8 * T.threshold) V := eσ ▸ hV
  have hρ : 0 < R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = T.threshold / 64
      rw [eσ]
    rw [e, hR.barrierFn_eq]
    exact hD.cut
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hrange := (G₁₁ R.coupling (b₁₁.trans hxc)).1
  have hform : (withEqualCouplings R).IsWellPosed :=
    { hasExpansions := hR.isStep.1
      admissible := hfit
      isCutoff := hcut
      range_le := Nat.le_succ _
      nextRange_le := Nat.le_succ _
      nextRange_ge := by
        show 2 ^ 16 ≤ clusterRange R.coupling
        omega
      range_ge_side := by
        show 2 ^ 40 * R.params.side ≤ clusterRange R.coupling
        rw [eL]
        omega
      range_ge_base := by
        show 4 * R.params.n₀ + 2 ^ 16 ≤ clusterRange R.coupling
        rw [en₀]
        omega
      coupling_pos := by
        show 0 < R.coupling
        linarith
      functional_spec := hArr }
  have hG : (coldCaseGround R V).IsAdmissibleGround := Or.inl ⟨hn, hV, rfl, rfl, rfl⟩
  have hw : (coldCaseGround R V).pairConstraint.IsActivityBounded ((coldCaseGround R V).referenceMeasure ∅)
      (coldCaseGround R V).weight ((coldCaseGround R V).spinActivity T.gasRate) := G₃ y b₃ R hR hx n _ hG _
  have hset := G₈ y b₈ R hR hx n _ hG
  have hmassS : ∀ σ, (coldCaseGround R V).pairConstraint.IsAdmissible σ →
      Integrable (fun η => (configSetting (coldCaseGround R V) σ).cutoffProduct η *
        Real.exp (-(configSetting (coldCaseGround R V) σ).potential η)) ∧
      0 < ∫ η, (configSetting (coldCaseGround R V) σ).cutoffProduct η *
        Real.exp (-(configSetting (coldCaseGround R V) σ).potential η) ∧
      settingMass (configSetting (coldCaseGround R V) σ) =
        ENNReal.ofReal (∫ η, (configSetting (coldCaseGround R V) σ).cutoffProduct η *
          Real.exp (-(configSetting (coldCaseGround R V) σ).potential η)) :=
    fun σ hs => G₄ y b₄ R hR n hnT _ (hset σ hs)
  have hf : GasFacts (coldCaseGround R V) ((coldCaseGround R V).spinActivity T.gasRate) :=
    { weight := hw
      prob := (hCL _ _ (coldCaseGround R V).pairConstraint ((coldCaseGround R V).referenceMeasure ∅)
        (coldCaseGround R V).weight ((coldCaseGround R V).spinActivity T.gasRate) hw).1
      setting := hset
      density_int := fun σ hs => (hmassS σ hs).1
      density_pos := fun σ hs => (hmassS σ hs).2.1
      mass := fun σ hs => (hmassS σ hs).2.2
      borel := G₆ y b₆ R hR hx n _ hG }
  have hDpos : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) := by
    have hσ := hfit.σ_pos
    have hnn : R.params.n₀ ≤ n * R.params.side :=
      hn.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))
    exact hR.isStep.1.1.positive _ hnn _ (isCold_trivialField _ hσ)
  have hCF : ColdFacts R V ((coldCaseGround R V).spinActivity T.gasRate) :=
    { base := ⟨hfit, hcut, hrow, hK⟩
      side := hside
      floor := hn
      weights := fun bad Yt b => hWB (withEqualCouplings R) hform n hn ∅ V bad Yt b
      gas := hf
      cases := (G₉ y b₉ R hR hx n _ hG).1
      image := fun B F hF => by
        rw [G₇ y b₇ R hR hx n _ hG B F hF (G₆ y b₆ R hR hx n _ hG F hF)]
        have e1 : ∏ X ∈ chainComponents R.nextRange (coldCaseGround R V).state.1,
            coarseFactor (coldCaseGround R V).coarse (coldCaseGround R V).state X = 1 := by
          have : chainComponents R.nextRange (coldCaseGround R V).state.1 = ∅ := by
            show chainComponents R.nextRange (∅ : Finset (TorusSite n)) = ∅
            unfold chainComponents
            simp
          rw [this, Finset.prod_empty]
        rw [e1, ENNReal.ofReal_one, mul_one]
      mean := fun F hm hg hi => ((G₁ y b₁ R hR hx n _ hG).2 F hm hg hi).2
      D_pos := hDpos
      marked := (G₅ y b₅ R hR hArr hx n hnT V hVT).1 Finset.univ }
  have hAr := hAt.admissible
  have hC₀ : 0 ≤ A.responseParams.C₀ := by
    have h1 := hAr.params_admissible.C₀_eq
    have h2 := hAr.params_admissible.N₀_nonneg
    have h3 := hAr.params_admissible.Kc_ge
    have h4 := hfit.a_ge
    rw [h1]
    linarith
  have hcount : ∀ Y : TorusSite n, ∑ θ ∈ supportsAtBlock R.params.side R.range Y,
      clusterWeight R.params.side T.gasRate R.coupling R.range θ *
        ((supportCore R.params.side R.range θ).card : ℝ) ^ 4 *
        Real.exp (2 * T.rt * (siteDiameter (supportCore R.params.side R.range θ) : ℝ)) ≤
      Real.exp (-(8 * T.gasRate * R.coupling)) := by
    have key : ∀ ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters, ℓ = T.stepParameters y → ∀ Y : TorusSite n,
        ∑ θ ∈ supportsAtBlock ℓ.side (clusterRange R.coupling) Y,
          clusterWeight ℓ.side T.gasRate R.coupling (clusterRange R.coupling) θ *
            ((supportCore ℓ.side (clusterRange R.coupling) θ).card : ℝ) ^ 4 *
            Real.exp (2 * T.rt * (siteDiameter (supportCore ℓ.side (clusterRange R.coupling) θ) : ℝ)) ≤
          Real.exp (-(8 * T.gasRate * R.coupling)) := by
      rintro _ rfl Y
      exact G₁₀ y b₁₀ R.coupling hxc n Y
    exact key R.params hR.params_eq
  have hxpos : 0 < R.coupling := by linarith
  have hchx : 0 ≤ T.gasRate * R.coupling := (mul_pos (gasRate_pos T hD) hxpos).le
  refine ⟨integrable_coldIntegrand hCF.base hCF.side V hCF.weights (f := fun _ _ _ => 1)
    (fun _ _ => measurable_const) (coldMass_ne_top hCF isCaseReal_one (gas_one_ne_top hCF)),
    coldWeightedIntegral_one_pos hCF, fun x₀ h => ?_, fun c => score_conditions hCF hsb c⟩
  refine response_properties hCF hAr.bounds hC₀ hAr.price.nonneg x₀ h
    (Finset.measurable_sum _ fun i _ =>
      (measurable_occupiedScore A hAr.price.borel i).comp (measurable_pi_apply i))
    (fun σ => chartSiteScore_le A hAr.price.nonneg _ (recordedSites_cold R V) σ x₀) ?_
  exact lintegral_occupiedScore_le hCF A hAr.price.borel x₀ (G₂ y b₂ R A hKA hAt n _ hG)
    (sum_spinActivity_le_one _ x₀ hD.rt_pos hchx (hcount _))
end YangMills.Construction.ResponseInTheExpansion
end
