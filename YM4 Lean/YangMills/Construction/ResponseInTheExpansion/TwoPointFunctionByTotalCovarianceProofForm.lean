import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelowProof
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TotalCovarianceOverAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.WeightedResponses.TwoPointCovariance
open YangMills.Construction.TorusFields YangMills.Construction.StepSettings YangMills.Construction.StepCosts YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ResponseInTheExpansion
section Abstract
variable {A D : Type} [MeasurableSpace A] [MeasurableSpace D] {μ : Measure A} {ρ : Measure D}
  [SFinite ρ] [IsProbabilityMeasure μ] {w : A × D → ℝ}
omit [IsProbabilityMeasure μ] in
theorem measurePreserving_fst_withDensity_prod (hw : Measurable w)
    (h1 : ∀ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) ∂ρ = 1) :
    MeasurePreserving (Prod.fst : A × D → A) ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) μ := by
  refine ⟨measurable_fst, ?_⟩
  ext B hB
  have hS : MeasurableSet ((Prod.fst : A × D → A) ⁻¹' B) := measurable_fst hB
  have hin : ∀ a, ∫⁻ d, ((Prod.fst : A × D → A) ⁻¹' B).indicator
      (fun u => ENNReal.ofReal (w u)) (a, d) ∂ρ = B.indicator 1 a := by
    intro a
    by_cases ha : a ∈ B
    · have e : ∀ d, ((Prod.fst : A × D → A) ⁻¹' B).indicator (fun u => ENNReal.ofReal (w u)) (a, d) =
          ENNReal.ofReal (w (a, d)) := fun d =>
        Set.indicator_of_mem (show (a, d) ∈ (Prod.fst : A × D → A) ⁻¹' B from ha) _
      simp only [e, h1, Set.indicator_of_mem ha, Pi.one_apply]
    · have e : ∀ d, ((Prod.fst : A × D → A) ⁻¹' B).indicator (fun u => ENNReal.ofReal (w u)) (a, d) = 0 :=
        fun d => Set.indicator_of_notMem (show (a, d) ∉ (Prod.fst : A × D → A) ⁻¹' B from ha) _
      simp only [e, lintegral_zero, Set.indicator_of_notMem ha]
  rw [Measure.map_apply measurable_fst hB, withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod _ (hw.ennreal_ofReal.indicator hS).aemeasurable]
  simp only [hin]
  exact lintegral_indicator_one hB
theorem integral_withDensity_prod (hw : Measurable w) (h0 : ∀ u, 0 ≤ w u) {g : A × D → ℝ}
    (hg : Integrable g ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u))) :
    ∫ u, g u ∂((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) =
      ∫ a, ∫ d, w (a, d) * g (a, d) ∂ρ ∂μ := by apply _root_.YangMills.SharedProofs.p3265 <;> assumption
end Abstract
section Outcomes
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
instance instFintypeBondSet (m : ℕ) [NeZero m] : Fintype (BondSet m) :=
  inferInstanceAs (Fintype (Finset (TorusBond m)))
theorem measurable_prod_slice {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {f : X × Y → ℝ}
    (hf : Measurable f) (x : X) : Measurable fun y => f (x, y) :=
  hf.comp measurable_prodMk_left
theorem measurable_of_stepOutcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
instance instIsFiniteMeasureStepReferenceMeasure (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (n : ℕ) [NeZero n] :
    IsFiniteMeasure (stepReferenceMeasure ℓ n) := by
  unfold stepReferenceMeasure
  infer_instance
theorem sum_bond_endpoints {n : ℕ} [NeZero n] (h : TorusSite n → ℝ) (A : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, h Y * ∑ i : Fin 4, (A (Y, i) + A (Y - TorusFields.unitStep n i, i)) =
      ∑ c : TorusBond n, (h c.1 + h (c.1 + TorusFields.unitStep n c.2)) * A c := by apply _root_.YangMills.SharedProofs.p11136 <;> assumption
def sourceWeight (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (c : TorusBond n) : ℝ :=
  ℓ.coupling / 2 * al * (blockMean ℓ.side (s + 1) n c.1 h + blockMean ℓ.side (s + 1) n (c.1 + TorusFields.unitStep n c.2) h)
theorem stepSourceTerm_eq_sum (x al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) :
    stepSourceTerm ℓ x al s h W d =
      ∑ c : TorusBond n, sourceWeight ℓ al s h c * bondScore ℓ x W d.2.1 d.1 c := by
  unfold stepSourceTerm sourceWeight
  rw [sum_bond_endpoints (fun Y => blockMean ℓ.side (s + 1) n Y h)
    (fun c => bondScore ℓ x W d.2.1 d.1 c), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
end Outcomes
section OneStep
variable (R : StepSetup) {n : ℕ} [NeZero n]
theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2 :=
  measurable_of_stepOutcome fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
theorem stepOutcomeDensity_nonneg (hS : StepTransitionDensityBounds) (hc : IsCutoff R.ballRadius R.barrierFn)
    (W : TorusField (n * R.params.side)) (d : StepOutcome R.params n) : 0 ≤ stepOutcomeDensity R W d := by apply _root_.YangMills.SharedProofs.p6753 <;> assumption
theorem integral_stepOutcomeDensity_mul (hS : StepTransitionDensityBounds) (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) {g : BaseChoice R.params.side n → TorusField n → ℝ}
    (hG : Measurable fun d : StepOutcome R.params n => g d.1 d.2.1) {C : ℝ} (hC : ∀ b V, |g b V| ≤ C) :
    ∫ d, stepOutcomeDensity R W d * g d.1 d.2.1 ∂(stepReferenceMeasure R.params n) =
      ∑ b : BaseChoice R.params.side n, ∫ V : TorusField n, g b V *
        WeightedResponses.stepTransitionDensity R.params R.coupling W b V ∂(fieldHaar n) := by apply _root_.YangMills.SharedProofs.p19566 <;> assumption
theorem measurable_stepSourceTerm (hSc : BondScoreProperties) (hf : R.params.Admissible) (al : ℝ) (s : ℕ)
    (h : PlaquetteWeight (fineSide R.params.side (s + 1) n)) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n =>
      stepSourceTerm R.params R.coupling al s h p.1 p.2 := by
  refine measurable_of_stepOutcome fun b bad => ?_
  have e : (fun p : TorusField (n * R.params.side) × TorusField n =>
      stepSourceTerm R.params R.coupling al s h p.1 (b, p.2, bad)) =
      fun p => ∑ c : TorusBond n, sourceWeight R.params al s h c * bondScore R.params R.coupling p.1 p.2 b c := by
    funext p
    exact stepSourceTerm_eq_sum R.coupling al s h p.1 (b, p.2, bad)
  rw [e]
  exact Finset.measurable_sum _ fun c _ => ((hSc R.params hf R.coupling n b c).2.2.2.2).const_mul _
theorem abs_stepSourceTerm_le (hSc : BondScoreProperties) (hf : R.params.Admissible) (al : ℝ) (s : ℕ)
    (h : PlaquetteWeight (fineSide R.params.side (s + 1) n)) (W : TorusField (n * R.params.side))
    (d : StepOutcome R.params n) :
    |stepSourceTerm R.params R.coupling al s h W d| ≤ ∑ c : TorusBond n, |sourceWeight R.params al s h c| * 2 := by
  rw [stepSourceTerm_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((hSc R.params hf R.coupling n d.1 c).2.2.1 W d.2.1) (abs_nonneg _)
theorem integral_stepOutcomeDensity_mul_source (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hSc : BondScoreProperties) (hf : R.params.Admissible)
    (hfl : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (al : ℝ) (s : ℕ) (h : PlaquetteWeight (fineSide R.params.side (s + 1) n))
    (W : TorusField (n * R.params.side)) :
    ∫ d, stepOutcomeDensity R W d * stepSourceTerm R.params R.coupling al s h W d
      ∂(stepReferenceMeasure R.params n) = 0 := by
  have hG : Measurable fun d : StepOutcome R.params n =>
      ∑ c : TorusBond n, sourceWeight R.params al s h c * bondScore R.params R.coupling W d.2.1 d.1 c := by
    have e : (fun d : StepOutcome R.params n =>
        ∑ c : TorusBond n, sourceWeight R.params al s h c * bondScore R.params R.coupling W d.2.1 d.1 c) =
        fun d => stepSourceTerm R.params R.coupling al s h W d := by
      funext d
      exact (stepSourceTerm_eq_sum R.coupling al s h W d).symm
    rw [e]
    exact measurable_prod_slice
      (f := fun p : TorusField (n * R.params.side) × StepOutcome R.params n =>
        stepSourceTerm R.params R.coupling al s h p.1 p.2)
      (measurable_stepSourceTerm R hSc hf al s h) W
  have hb : ∀ (b : BaseChoice R.params.side n) (V : TorusField n),
      |∑ c : TorusBond n, sourceWeight R.params al s h c * bondScore R.params R.coupling W V b c| ≤
        ∑ c : TorusBond n, |sourceWeight R.params al s h c| * 2 := by
    intro b V
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hSc R.params hf R.coupling n b c).2.2.1 W V) (abs_nonneg _)
  have h1 := integral_stepOutcomeDensity_mul R hS hc hB W
    (g := fun b V => ∑ c : TorusBond n, sourceWeight R.params al s h c * bondScore R.params R.coupling W V b c) hG hb
  have h2 := hM R.params hf hfl R.coupling n W 1 (fun _ => 0) (fun _ c => sourceWeight R.params al s h c)
    (fun c i i' hne => absurd (Subsingleton.elim i i') hne)
  simp only [Fin.prod_univ_one, zero_add] at h2
  have e : ∫ d, stepOutcomeDensity R W d * stepSourceTerm R.params R.coupling al s h W d
      ∂(stepReferenceMeasure R.params n) =
      ∫ d, stepOutcomeDensity R W d *
        ∑ c : TorusBond n, sourceWeight R.params al s h c * bondScore R.params R.coupling W d.2.1 d.1 c
          ∂(stepReferenceMeasure R.params n) :=
    integral_congr_ae (Filter.Eventually.of_forall fun d =>
      congrArg _ (stepSourceTerm_eq_sum R.coupling al s h W d))
  exact e.trans (h1.trans h2)
end OneStep
section Chain
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
theorem topField_measurable (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
theorem stage_isCutoff (T : StageTower ℓ) (h : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
def stageStepDensity (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n) : ℝ :=
  stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2
variable (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
  (hSc : BondScoreProperties) (hSt : StageStatesMeasurableStatement)
  (hf : ℓ.Admissible) (hfl : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (T : StageTower ℓ)
  (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hcoin : T.MarksMeasurable) (β : ℝ) (al : ℕ → ℝ)
include hS hcoin in
theorem measurable_stageStepDensity (s n : ℕ) [NeZero n] : Measurable (stageStepDensity T s n) := by apply _root_.YangMills.DeltaSharedProofs.p500627 <;> assumption
include hS hcut in
theorem stageStepDensity_nonneg (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n) :
    0 ≤ stageStepDensity T s n u :=
  stepOutcomeDensity_nonneg (T.stage s).toStepSetup hS (stage_isCutoff T hcut s) _ _
include hS hM hf hfl hcut hcoin in
theorem isProbabilityMeasure_markedSampleLaw (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β s n) := by apply _root_.YangMills.SharedProofs.p20096 <;> assumption
include hS hM hf hfl hcut hcoin in
theorem measurePreserving_markedSample_fst (s n : ℕ) [NeZero n] :
    MeasurePreserving (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)
      (markedSampleLaw T β s (n * ℓ.side)) := by apply _root_.YangMills.SharedProofs.p11229 <;> assumption
include hSc hf in
theorem measurable_sourceTerm (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) :
    Measurable (sourceTerm T al s n h) := by
  have h1 := measurable_stepSourceTerm (T.stage s).toStepSetup (n := n) hSc hf (al s) s h
  have h2 : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
      ((topField ℓ s (n * ℓ.side) u.1, u.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
    ((topField_measurable s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd
  have h3 := h1.comp h2
  exact h3
include hSc hf in
theorem abs_sourceTerm_le (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (u : MarkedSample ℓ (s + 1) n) :
    |sourceTerm T al s n h u| ≤ ∑ c : TorusBond n, |sourceWeight ℓ (al s) s h c| * 2 :=
  abs_stepSourceTerm_le (T.stage s).toStepSetup hSc hf (al s) s h _ _
include hS hM hSc hf hfl hcut hcoin in
theorem integral_mul_sourceTerm (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    {φ : MarkedSample ℓ s (n * ℓ.side) → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hb : ∀ᵐ a ∂(markedSampleLaw T β s (n * ℓ.side)), |φ a| ≤ C) :
    ∫ u, φ u.1 * sourceTerm T al s n h u ∂(markedSampleLaw T β (s + 1) n) = 0 := by
  have := isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β s (n * ℓ.side)
  have := isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β (s + 1) n
  have hπ := measurePreserving_markedSample_fst hS hM hf hfl T hcut hcoin β s n
  have hbπ : ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n), |φ u.1| ≤ C := hπ.quasiMeasurePreserving.ae hb
  have hmS := measurable_sourceTerm hSc hf T al s n h
  have hφ' : Measurable fun u : MarkedSample ℓ (s + 1) n => φ u.1 := hφ.comp hπ.measurable
  have hI : Integrable (fun u : MarkedSample ℓ (s + 1) n => φ u.1 * sourceTerm T al s n h u)
      (markedSampleLaw T β (s + 1) n) := by
    refine Integrable.of_bound (hφ'.mul hmS).aestronglyMeasurable
      (C * ∑ c : TorusBond n, |sourceWeight ℓ (al s) s h c| * 2) ?_
    filter_upwards [hbπ] with u hu
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hu (abs_sourceTerm_le hSc hf T al s n h u) (abs_nonneg _) ((abs_nonneg _).trans hu)
  have e := integral_withDensity_prod (μ := markedSampleLaw T β s (n * ℓ.side)) (ρ := stepReferenceMeasure ℓ n)
    (w := stageStepDensity T s n)
    (measurable_stageStepDensity hS T hcoin s n) (stageStepDensity_nonneg hS T hcut s n)
    (g := fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => φ u.1 * sourceTerm T al s n h u) hI
  have inner : ∀ a : MarkedSample ℓ s (n * ℓ.side),
      ∫ d, stageStepDensity T s n (a, d) * (φ a * sourceTerm T al s n h (a, d)) ∂(stepReferenceMeasure ℓ n) = 0 := by
    intro a
    have h0 := integral_stepOutcomeDensity_mul_source (T.stage s).toStepSetup (n := n) hS hM hSc hf hfl
      (stage_isCutoff T hcut s) (fun bad => hcoin s n bad) (al s) s h (topField ℓ s (n * ℓ.side) a)
    have e1 : ∫ d, stageStepDensity T s n (a, d) * (φ a * sourceTerm T al s n h (a, d))
        ∂(stepReferenceMeasure ℓ n) =
        ∫ d, φ a * (stageStepDensity T s n (a, d) * sourceTerm T al s n h (a, d)) ∂(stepReferenceMeasure ℓ n) :=
      integral_congr_ae (Filter.Eventually.of_forall fun d => by
        show stageStepDensity T s n (a, d) * (φ a * sourceTerm T al s n h (a, d)) =
          φ a * (stageStepDensity T s n (a, d) * sourceTerm T al s n h (a, d))
        ring)
    rw [e1, integral_const_mul]
    have h0' : ∫ d, stageStepDensity T s n (a, d) * sourceTerm T al s n h (a, d)
        ∂(stepReferenceMeasure ℓ n) = 0 := h0
    rw [h0', mul_zero]
  have e2 : ∫ a, ∫ d, stageStepDensity T s n (a, d) * (φ a * sourceTerm T al s n h (a, d))
      ∂(stepReferenceMeasure ℓ n) ∂(markedSampleLaw T β s (n * ℓ.side)) = 0 := by
    simp only [inner]
    exact integral_zero _ _
  exact e.trans e2
include hS hM hSc hf hfl hcut hcoin in
theorem integral_sourceTerm (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) :
    ∫ u, sourceTerm T al s n h u ∂(markedSampleLaw T β (s + 1) n) = 0 := by
  have h1 := integral_mul_sourceTerm hS hM hSc hf hfl T hcut hcoin β al s n h (φ := fun _ => 1)
    measurable_const (C := 1) (Filter.Eventually.of_forall fun _ => (abs_one (α := ℝ)).le)
  simpa only [one_mul] using h1
theorem response_succ_eq (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) :
    response T β al (s + 1) n h =
      (markedSampleLaw T β (s + 1) n)[stepSum T β al s n h | stageSigma T (s + 1) n] := by
  funext u
  rfl
include hS hM hSc hSt hf hfl hcut hcoin in
theorem response_measurable_bounded (s : ℕ) : ∀ (n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)),
    Measurable (response T β al s n h) ∧
      ∃ C : ℝ, ∀ᵐ u ∂(markedSampleLaw T β s n), |response T β al s n h u| ≤ C := by apply _root_.YangMills.SharedProofs.p50239 <;> assumption
theorem bottomField_measurable (s : ℕ) : ∀ n : ℕ, Measurable (bottomField ℓ s n) := by apply _root_.YangMills.SharedProofs.p4086 <;> assumption
include hS hM hf hfl hcut hcoin in
theorem map_bottomField (s : ℕ) : ∀ (n : ℕ) [NeZero n],
    Measure.map (bottomField ℓ s n) (markedSampleLaw T β s n) = wilsonLaw β (fineSide ℓ.side s n) := by
  induction s with
  | zero =>
    intro n _
    exact Measure.map_id
  | succ s ih =>
    intro n _
    have hπ := measurePreserving_markedSample_fst hS hM hf hfl T hcut hcoin β s n
    have e := Measure.map_map (μ := markedSampleLaw T β (s + 1) n)
      (bottomField_measurable s (n * ℓ.side)) hπ.measurable
    have e2 : Measure.map (bottomField ℓ (s + 1) n) (markedSampleLaw T β (s + 1) n) =
        Measure.map (bottomField ℓ s (n * ℓ.side))
          (Measure.map (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)) := e.symm
    rw [e2, hπ.map_eq]
    exact ih (n * ℓ.side)
theorem finalField_measurable (s n : ℕ) : Measurable (finalField ℓ s n) := by
  cases s with
  | zero => exact measurable_id
  | succ s =>
    exact show Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n => u.2.2 from
      measurable_snd.comp measurable_snd
theorem forgetMarks_measurable (s : ℕ) : ∀ n : ℕ, Measurable (forgetMarks ℓ s n) := by apply _root_.YangMills.SharedProofs.p23598 <;> assumption
theorem finalField_forgetMarks (s n : ℕ) (u : MarkedSample ℓ s n) :
    finalField ℓ s n (forgetMarks ℓ s n u) = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p8091 <;> assumption
theorem chainJointLaw_zero (x : ℕ → ℝ) (β : ℝ) (n : ℕ) [NeZero n] :
    chainJointLaw ℓ β x 0 n = wilsonLaw β n := by
  have hn : n ≠ 0 := NeZero.ne n
  have e : ∀ W : TorusField n, wilsonWeight β n W = Real.exp (-β * wilsonAction Finset.univ W) := by
    intro W
    simp only [wilsonWeight, dif_neg hn]
  show (fieldHaar n).withDensity _ = (fieldHaar n).withDensity _
  congr 1
  funext W
  show ENNReal.ofReal (wilsonWeight β n W / ∫ W', wilsonWeight β n W' ∂(fieldHaar n)) = _
  simp only [e]
  rw [e W]
include hS hM hf hfl hcut hcoin in
theorem map_forgetMarks (hMean : ChainStepMean) (s : ℕ) : ∀ (n : ℕ) [NeZero n],
    Measure.map (forgetMarks ℓ s n) (markedSampleLaw T β s n) =
      chainJointLaw ℓ β (fun j => (T.stage j).coupling) s n := by
  induction s with
  | zero =>
    intro n _
    exact Measure.map_id.trans (chainJointLaw_zero _ β n).symm
  | succ s ih =>
    intro n _
    set x : ℕ → ℝ := fun j => (T.stage j).coupling with hx
    have hp : IsProbabilityMeasure (markedSampleLaw T β s (n * ℓ.side)) :=
      isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β s (n * ℓ.side)
    have hp' : IsProbabilityMeasure (markedSampleLaw T β (s + 1) n) :=
      isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β (s + 1) n
    obtain ⟨hfin, -, hstep⟩ := hMean ℓ β x
    have hc' : IsFiniteMeasure (chainJointLaw ℓ β x (s + 1) n) := hfin (s + 1) n
    have hwc := forgetMarks_measurable (ℓ := ℓ) (s + 1) n
    have hwc0 := forgetMarks_measurable (ℓ := ℓ) s (n * ℓ.side)
    refine Measure.ext fun A hA => ?_
    have hF : Measurable (A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ)) := measurable_one.indicator hA
    have hFb : ∀ u, |A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) u| ≤ 1 := by
      intro u
      by_cases h : u ∈ A <;> simp [h]
    let G : ChainSample ℓ s (n * ℓ.side) → ℝ := fun c => ∑ b : BaseChoice ℓ.side n, ∫ V : TorusField n,
      A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) (c, b, V) *
        WeightedResponses.stepTransitionDensity ℓ (x s) (finalField ℓ s (n * ℓ.side) c) b V ∂(fieldHaar n)
    have hG : Measurable G := by
      refine Finset.measurable_sum _ fun b _ => ?_
      have hj : Measurable fun p : ChainSample ℓ s (n * ℓ.side) × TorusField n =>
          A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) (p.1, b, p.2) *
            WeightedResponses.stepTransitionDensity ℓ (x s) (finalField ℓ s (n * ℓ.side) p.1) b p.2 := by
        have h1 : Measurable fun p : ChainSample ℓ s (n * ℓ.side) × TorusField n =>
            ((p.1, b, p.2) : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n) :=
          measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
        have h2 : Measurable fun p : ChainSample ℓ s (n * ℓ.side) × TorusField n =>
            ((finalField ℓ s (n * ℓ.side) p.1, p.2) : TorusField (n * ℓ.side) × TorusField n) :=
          ((finalField_measurable s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd
        have h3 := ((hS ℓ (x s) n).1 b).comp h2
        have h4 := hF.comp h1
        exact h4.mul h3
      exact (hj.stronglyMeasurable.integral_prod_right (ν := fieldHaar n)).measurable
    have hchain := hstep s n _ G hF ⟨1, hFb⟩ (fun _ => rfl)
    have hR := stage_isCutoff T hcut s
    have hB : ∀ bad : Finset (TorusBond (n * ℓ.side)),
        Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
          markLaw (T.stage s).toStepSetup p.1 p.2 bad :=
      fun bad => hcoin s n bad
    have hIn : Integrable (fun u : MarkedSample ℓ (s + 1) n =>
        A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) (forgetMarks ℓ (s + 1) n u))
        (markedSampleLaw T β (s + 1) n) :=
      Integrable.of_bound (hF.comp hwc).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hFb _)
    have e := integral_withDensity_prod (μ := markedSampleLaw T β s (n * ℓ.side)) (ρ := stepReferenceMeasure ℓ n)
      (w := stageStepDensity T s n)
      (measurable_stageStepDensity hS T hcoin s n) (stageStepDensity_nonneg hS T hcut s n)
      (g := fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) (forgetMarks ℓ s (n * ℓ.side) u.1, u.2.1, u.2.2.1)) hIn
    have inner : ∀ a : MarkedSample ℓ s (n * ℓ.side),
        ∫ d, stageStepDensity T s n (a, d) * A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ)
          (forgetMarks ℓ s (n * ℓ.side) a, d.1, d.2.1) ∂(stepReferenceMeasure ℓ n) =
            G (forgetMarks ℓ s (n * ℓ.side) a) := by
      intro a
      have hmg : Measurable fun d : StepOutcome ℓ n =>
          A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) (forgetMarks ℓ s (n * ℓ.side) a, d.1, d.2.1) := by
        have h1 : Measurable fun d : StepOutcome ℓ n =>
            ((forgetMarks ℓ s (n * ℓ.side) a, d.1, d.2.1) :
              ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n) :=
          measurable_const.prodMk (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
        exact hF.comp h1
      have h0 := integral_stepOutcomeDensity_mul (T.stage s).toStepSetup (n := n) hS hR hB
        (topField ℓ s (n * ℓ.side) a)
        (g := fun b V => A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) (forgetMarks ℓ s (n * ℓ.side) a, b, V))
        hmg (C := 1) (fun _ _ => hFb _)
      refine h0.trans ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [finalField_forgetMarks]
    have e2 : ∫ a, ∫ d, stageStepDensity T s n (a, d) * A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ)
        (forgetMarks ℓ s (n * ℓ.side) a, d.1, d.2.1) ∂(stepReferenceMeasure ℓ n)
          ∂(markedSampleLaw T β s (n * ℓ.side)) =
        ∫ a, G (forgetMarks ℓ s (n * ℓ.side) a) ∂(markedSampleLaw T β s (n * ℓ.side)) := by
      simp only [inner]
    have e3 : ∫ a, G (forgetMarks ℓ s (n * ℓ.side) a) ∂(markedSampleLaw T β s (n * ℓ.side)) =
        ∫ c, G c ∂(chainJointLaw ℓ β x s (n * ℓ.side)) := by
      rw [← ih (n * ℓ.side)]
      exact (integral_map hwc0.aemeasurable hG.aestronglyMeasurable).symm
    have hl : ∫ u, A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) (forgetMarks ℓ (s + 1) n u)
        ∂(markedSampleLaw T β (s + 1) n) = ∫ u, A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) u
          ∂(chainJointLaw ℓ β x (s + 1) n) := (e.trans (e2.trans e3)).trans hchain.symm
    have hi1 : ∫ u, A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) u ∂(chainJointLaw ℓ β x (s + 1) n) =
        (chainJointLaw ℓ β x (s + 1) n).real A := integral_indicator_one hA
    have hi2 : ∫ u, A.indicator (1 : ChainSample ℓ (s + 1) n → ℝ) (forgetMarks ℓ (s + 1) n u)
        ∂(markedSampleLaw T β (s + 1) n) =
          (Measure.map (forgetMarks ℓ (s + 1) n) (markedSampleLaw T β (s + 1) n)).real A := by
      rw [← integral_indicator_one hA]
      exact (integral_map hwc.aemeasurable hF.aestronglyMeasurable).symm
    have hfm : IsFiniteMeasure (Measure.map (forgetMarks ℓ (s + 1) n) (markedSampleLaw T β (s + 1) n)) :=
      Measure.isFiniteMeasure_map _ _
    have hr : (Measure.map (forgetMarks ℓ (s + 1) n) (markedSampleLaw T β (s + 1) n)).real A =
        (chainJointLaw ℓ β x (s + 1) n).real A := by
      rw [← hi1, ← hi2, hl]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hr
include hS hM hSc hf hfl hcut hcoin in
theorem integral_sourceTerm_mul (hTwo : ScoreSumCovariance) (s n : ℕ) [NeZero n]
    (h₁ h₂ : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) :
    ∫ u, sourceTerm T al s n h₁ u * sourceTerm T al s n h₂ u ∂(markedSampleLaw T β (s + 1) n) =
      ∫ a, (ℓ.coupling * al s) ^ 2 * ∑ c : TorusBond n,
        bondBlockMean ℓ.side (s + 1) n h₁ c * bondBlockMean ℓ.side (s + 1) n h₂ c *
        ∑ b : BaseChoice ℓ.side n, ∫ V : TorusField n,
          bondScoreVariance ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) a) b c *
            WeightedResponses.stepTransitionDensity ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) a) b V
              ∂(fieldHaar n)
        ∂(markedSampleLaw T β s (n * ℓ.side)) := by
  have hp : IsProbabilityMeasure (markedSampleLaw T β s (n * ℓ.side)) :=
    isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β s (n * ℓ.side)
  have hp' : IsProbabilityMeasure (markedSampleLaw T β (s + 1) n) :=
    isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β (s + 1) n
  have hm₁ := measurable_sourceTerm hSc hf T al s n h₁
  have hm₂ := measurable_sourceTerm hSc hf T al s n h₂
  have hI : Integrable (fun u : MarkedSample ℓ (s + 1) n => sourceTerm T al s n h₁ u * sourceTerm T al s n h₂ u)
      (markedSampleLaw T β (s + 1) n) := by
    refine Integrable.of_bound (hm₁.mul hm₂).aestronglyMeasurable
      ((∑ c : TorusBond n, |sourceWeight ℓ (al s) s h₁ c| * 2) *
        ∑ c : TorusBond n, |sourceWeight ℓ (al s) s h₂ c| * 2)
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_sourceTerm_le hSc hf T al s n h₁ u) (abs_sourceTerm_le hSc hf T al s n h₂ u)
      (abs_nonneg _) ((abs_nonneg _).trans (abs_sourceTerm_le hSc hf T al s n h₁ u))
  have e := integral_withDensity_prod (μ := markedSampleLaw T β s (n * ℓ.side)) (ρ := stepReferenceMeasure ℓ n)
    (w := stageStepDensity T s n)
    (measurable_stageStepDensity hS T hcoin s n) (stageStepDensity_nonneg hS T hcut s n)
    (g := fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
      sourceTerm T al s n h₁ u * sourceTerm T al s n h₂ u) hI
  refine e.trans (integral_congr_ae (Filter.Eventually.of_forall fun a => ?_))
  show ∫ d, stageStepDensity T s n (a, d) * (sourceTerm T al s n h₁ (a, d) * sourceTerm T al s n h₂ (a, d))
    ∂(stepReferenceMeasure ℓ n) = _
  set W := topField ℓ s (n * ℓ.side) a with hW
  set x := (T.stage s).coupling with hx
  set v₁ := sourceWeight ℓ (al s) s h₁ with hv₁
  set v₂ := sourceWeight ℓ (al s) s h₂ with hv₂
  have hR := stage_isCutoff T hcut s
  have hB : ∀ bad : Finset (TorusBond (n * ℓ.side)),
      Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
        markLaw (T.stage s).toStepSetup p.1 p.2 bad :=
    fun bad => hcoin s n bad
  have hsrc : ∀ (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (d : StepOutcome ℓ n),
      sourceTerm T al s n h (a, d) =
        ∑ c : TorusBond n, sourceWeight ℓ (al s) s h c * bondScore ℓ x W d.2.1 d.1 c :=
    fun h d => stepSourceTerm_eq_sum x (al s) s h W d
  have hmg : Measurable fun d : StepOutcome ℓ n =>
      (∑ c : TorusBond n, v₁ c * bondScore ℓ x W d.2.1 d.1 c) *
        ∑ c : TorusBond n, v₂ c * bondScore ℓ x W d.2.1 d.1 c := by
    have e1 : ∀ h : PlaquetteWeight (fineSide ℓ.side (s + 1) n),
        Measurable fun d : StepOutcome ℓ n =>
          ∑ c : TorusBond n, sourceWeight ℓ (al s) s h c * bondScore ℓ x W d.2.1 d.1 c := by
      intro h
      have e2 : (fun d : StepOutcome ℓ n =>
          ∑ c : TorusBond n, sourceWeight ℓ (al s) s h c * bondScore ℓ x W d.2.1 d.1 c) =
          fun d => stepSourceTerm ℓ x (al s) s h W d := by
        funext d
        exact (stepSourceTerm_eq_sum x (al s) s h W d).symm
      rw [e2]
      exact measurable_prod_slice
        (f := fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n => stepSourceTerm ℓ x (al s) s h p.1 p.2)
        (measurable_stepSourceTerm (T.stage s).toStepSetup hSc hf (al s) s h) W
    exact (e1 h₁).mul (e1 h₂)
  have hbd : ∀ (b : BaseChoice ℓ.side n) (V : TorusField n),
      |(∑ c : TorusBond n, v₁ c * bondScore ℓ x W V b c) * ∑ c : TorusBond n, v₂ c * bondScore ℓ x W V b c| ≤
        (∑ c : TorusBond n, |v₁ c| * 2) * ∑ c : TorusBond n, |v₂ c| * 2 := by
    intro b V
    have e1 : ∀ v : TorusBond n → ℝ,
        |∑ c : TorusBond n, v c * bondScore ℓ x W V b c| ≤ ∑ c : TorusBond n, |v c| * 2 := by
      intro v
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((hSc ℓ hf x n b c).2.2.1 W V) (abs_nonneg _)
    rw [abs_mul]
    exact mul_le_mul (e1 v₁) (e1 v₂) (abs_nonneg _) ((abs_nonneg _).trans (e1 v₁))
  have h1 := integral_stepOutcomeDensity_mul (T.stage s).toStepSetup (n := n) hS hR hB W
    (g := fun b V => (∑ c : TorusBond n, v₁ c * bondScore ℓ x W V b c) *
      ∑ c : TorusBond n, v₂ c * bondScore ℓ x W V b c)
    hmg hbd
  have h2 := hTwo ℓ hf x n W v₁ v₂
  have e0 : ∫ d, stageStepDensity T s n (a, d) * (sourceTerm T al s n h₁ (a, d) * sourceTerm T al s n h₂ (a, d))
      ∂(stepReferenceMeasure ℓ n) =
      ∫ d, stepOutcomeDensity (T.stage s).toStepSetup W d *
        ((∑ c : TorusBond n, v₁ c * bondScore ℓ x W d.2.1 d.1 c) *
          ∑ c : TorusBond n, v₂ c * bondScore ℓ x W d.2.1 d.1 c) ∂(stepReferenceMeasure ℓ n) :=
    integral_congr_ae (Filter.Eventually.of_forall fun d => by
      show stageStepDensity T s n (a, d) * (sourceTerm T al s n h₁ (a, d) * sourceTerm T al s n h₂ (a, d)) = _
      rw [hsrc h₁ d, hsrc h₂ d]
      rfl)
  refine e0.trans (h1.trans (h2.trans ?_))
  beta_reduce
  rw [← hW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : v₁ c * v₂ c =
      (ℓ.coupling * al s) ^ 2 * (bondBlockMean ℓ.side (s + 1) n h₁ c * bondBlockMean ℓ.side (s + 1) n h₂ c) := by
    simp only [hv₁, hv₂, sourceWeight, bondBlockMean]
    ring
  rw [e1]
  ring
end Chain
theorem twoPointByTotalCovariance (hcov : LawOfTotalCovarianceWithIncrement)
    (hSt : StageStatesMeasurableStatement) (hM : ScoreProductStepMean)
    (hS : StepTransitionDensityBounds) (hSc : BondScoreProperties)
    (hMean : ChainStepMean) (hTwo : ScoreSumCovariance) :
    TwoPointByTotalCovarianceStatement := by
  intro ℓ hf hfl T hcut hcoin β al s n _
  refine ⟨isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β s n, (hSt ℓ hf T s n).comap_le,
    map_bottomField hS hM hf hfl T hcut hcoin β s n, map_forgetMarks hS hM hf hfl T hcut hcoin β hMean s n,
    integral_sourceTerm_mul hS hM hSc hf hfl T hcut hcoin β al hTwo s n, ?_⟩
  revert n
  induction s with
  | zero =>
    intro n _ f₁ f₂
    exact (add_zero _).symm
  | succ s ih =>
    intro n _ f₁ f₂
    have := isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β s (n * ℓ.side)
    have := isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β (s + 1) n
    have hG : stageSigma T (s + 1) n ≤ markedSampleMeasurableSpace ℓ (s + 1) n :=
      (hSt ℓ hf T (s + 1) n).comap_le
    have hπ := measurePreserving_markedSample_fst hS hM hf hfl T hcut hcoin β s n
    obtain ⟨hm₁, C₁, hC₁⟩ := response_measurable_bounded hS hM hSc hSt hf hfl T hcut hcoin β al s (n * ℓ.side) f₁
    obtain ⟨hm₂, C₂, hC₂⟩ := response_measurable_bounded hS hM hSc hSt hf hfl T hcut hcoin β al s (n * ℓ.side) f₂
    set K₁ : ℝ := ∑ c : TorusBond n, |sourceWeight ℓ (al s) s f₁ c| * 2 with hK₁
    set K₂ : ℝ := ∑ c : TorusBond n, |sourceWeight ℓ (al s) s f₂ c| * 2 with hK₂
    have core := hcov (MarkedSample ℓ s (n * ℓ.side)) (MarkedSample ℓ (s + 1) n) (stageSigma T (s + 1) n)
      (markedSampleLaw T β s (n * ℓ.side)) (markedSampleLaw T β (s + 1) n) (fun u => u.1)
      (response T β al s (n * ℓ.side) f₁) (response T β al s (n * ℓ.side) f₂)
      (sourceTerm T al s n f₁) (sourceTerm T al s n f₂) (max (max C₁ C₂) (max K₁ K₂))
      hπ hG hm₁.aestronglyMeasurable hm₂.aestronglyMeasurable
      (hC₁.mono fun a h => h.trans ((le_max_left _ _).trans (le_max_left _ _)))
      (hC₂.mono fun a h => h.trans ((le_max_right _ _).trans (le_max_left _ _)))
      (measurable_sourceTerm hSc hf T al s n f₁).aestronglyMeasurable
      (measurable_sourceTerm hSc hf T al s n f₂).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => (abs_sourceTerm_le hSc hf T al s n f₁ u).trans
        ((le_max_left _ _).trans (le_max_right _ _)))
      (Filter.Eventually.of_forall fun u => (abs_sourceTerm_le hSc hf T al s n f₂ u).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
      (integral_sourceTerm hS hM hSc hf hfl T hcut hcoin β al s n f₁)
      (integral_sourceTerm hS hM hSc hf hfl T hcut hcoin β al s n f₂)
      (integral_mul_sourceTerm hS hM hSc hf hfl T hcut hcoin β al s n f₁ hm₂ hC₂)
      (integral_mul_sourceTerm hS hM hSc hf hfl T hcut hcoin β al s n f₂ hm₁ hC₁)
    have e1 : cov[response T β al s (n * ℓ.side) f₁, response T β al s (n * ℓ.side) f₂;
        markedSampleLaw T β s (n * ℓ.side)] =
        cov[response T β al (s + 1) n f₁, response T β al (s + 1) n f₂; markedSampleLaw T β (s + 1) n] +
          stepCovarianceTerm T β al s n f₁ f₂ := by
      rw [response_succ_eq, response_succ_eq]
      exact core
    have key : cov[curvatureObservable f₁, curvatureObservable f₂; wilsonLaw β (fineSide ℓ.side s (n * ℓ.side))] =
        cov[response T β al (s + 1) n f₁, response T β al (s + 1) n f₂; markedSampleLaw T β (s + 1) n] +
          (covarianceSum T β al s (n * ℓ.side) f₁ f₂ + stepCovarianceTerm T β al s n f₁ f₂) := by
      refine (ih (n * ℓ.side) f₁ f₂).trans ?_
      rw [e1]
      ring
    exact key
end YangMills.Construction.WeightedResponses.TwoPointCovariance
end
