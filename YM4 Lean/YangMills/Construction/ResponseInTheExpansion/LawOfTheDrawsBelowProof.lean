import YangMills.Construction.FreeEnergiesOfTheFlow.ThePastIsFreeGivenTheStateProof
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelow
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheCopiesAtNoLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusFields YangMills.Construction.StepSettings YangMills.Construction.StepCosts YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ResponseInTheExpansion
section Abstract
variable {A D : Type} [MeasurableSpace A] [MeasurableSpace D] {μ : Measure A} {ρ : Measure D}
  [SFinite ρ] [IsProbabilityMeasure μ] {w : A × D → ℝ}
private theorem withDensity_prod_isProbabilityMeasure (hw : Measurable w)
    (h1 : ∀ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) ∂ρ = 1) :
    IsProbabilityMeasure ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) := by apply _root_.YangMills.SharedProofs.p11113 <;> assumption
private theorem measurePreserving_fst_withDensity_prod (hw : Measurable w)
    (h1 : ∀ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) ∂ρ = 1) :
    MeasurePreserving (Prod.fst : A × D → A) ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) μ := by apply _root_.YangMills.SharedProofs.p1188 <;> assumption
end Abstract
section Outcomes
variable {ℓ : TorusLumps.StepParameters}
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private theorem measurable_of_stepOutcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private instance (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] :
    IsFiniteMeasure (stepReferenceMeasure ℓ n) := by
  unfold stepReferenceMeasure
  infer_instance
private theorem sum_mul_sum_bond_ends {n : ℕ} [NeZero n] (h : TorusSite n → ℝ) (A : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, h Y * ∑ i : Fin 4, (A (Y, i) + A (Y - unitStep n i, i)) =
      ∑ c : TorusBond n, (h c.1 + h (c.1 + unitStep n c.2)) * A c := by apply _root_.YangMills.SharedProofs.p11136 <;> assumption
private def bondSourceCoeff (ℓ : TorusLumps.StepParameters) (al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (c : TorusBond n) : ℝ :=
  ℓ.coupling / 2 * al * (blockMean ℓ.side (s + 1) n c.1 h + blockMean ℓ.side (s + 1) n (c.1 + unitStep n c.2) h)
private theorem stepSourceTerm_eq_sum (x al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) :
    stepSourceTerm ℓ x al s h W d =
      ∑ c : TorusBond n, bondSourceCoeff ℓ al s h c * bondScore ℓ x W d.2.1 d.1 c := by
  unfold stepSourceTerm bondSourceCoeff
  rw [sum_mul_sum_bond_ends (fun Y => blockMean ℓ.side (s + 1) n Y h)
    (fun c => bondScore ℓ x W d.2.1 d.1 c), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
end Outcomes
section OneStep
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2 :=
  measurable_of_stepOutcome fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
private theorem lintegral_stepOutcomeDensity (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hf : R.params.Admissible) (hfl : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) :
    ∫⁻ d, ENNReal.ofReal (stepOutcomeDensity R W d) ∂(stepReferenceMeasure R.params n) = 1 := by apply _root_.YangMills.SharedProofs.p27860 <;> assumption
private theorem abs_stepSourceTerm_le (hSc : BondScoreProperties) (hf : R.params.Admissible) (al : ℝ) (s : ℕ)
    (h : PlaquetteWeight (fineSide R.params.side (s + 1) n)) (W : TorusField (n * R.params.side))
    (d : StepOutcome R.params n) :
    |stepSourceTerm R.params R.coupling al s h W d| ≤ ∑ c : TorusBond n, |bondSourceCoeff R.params al s h c| * 2 := by
  rw [stepSourceTerm_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((hSc R.params hf R.coupling n d.1 c).2.2.1 W d.2.1) (abs_nonneg _)
end OneStep
section Chain
variable {ℓ : TorusLumps.StepParameters}
private theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private theorem stage_isCutoff (T : StageTower ℓ) (h : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
private theorem wilsonLaw_isProbability (β : ℝ) (m : ℕ) [NeZero m] : IsProbabilityMeasure (wilsonLaw β m) := by apply _root_.YangMills.SharedProofs.p1521 <;> assumption
private theorem continuous_curvatureObservable {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    Continuous (curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p1196 <;> assumption
private def stageStepDensity (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n) : ℝ :=
  stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2
variable (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
  (hSc : BondScoreProperties) (hSt : StageStatesMeasurableStatement)
  (hf : ℓ.Admissible) (hfl : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (T : StageTower ℓ)
  (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hcoin : T.MarksMeasurable) (β : ℝ) (al : ℕ → ℝ)
include hS hcoin in
private theorem measurable_stageStepDensity (s n : ℕ) [NeZero n] : Measurable (stageStepDensity T s n) := by
  have h1 := measurable_stepOutcomeDensity (T.stage s).toStepSetup (n := n) hS (fun bad => hcoin s n bad)
  have h2 : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
      ((topField ℓ s (n * ℓ.side) u.1, u.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
    ((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd
  have h3 := h1.comp h2
  exact h3
abbrev _root_.YangMills.DeltaSharedProofs.p500627 := @measurable_stageStepDensity
include hS hM hf hfl hcut hcoin in
private theorem lintegral_stageStepDensity (s n : ℕ) [NeZero n] (a : MarkedSample ℓ s (n * ℓ.side)) :
    ∫⁻ d, ENNReal.ofReal (stageStepDensity T s n (a, d)) ∂(stepReferenceMeasure ℓ n) = 1 :=
  lintegral_stepOutcomeDensity (T.stage s).toStepSetup hS hM hf hfl (stage_isCutoff T hcut s)
    (fun bad => hcoin s n bad) (topField ℓ s (n * ℓ.side) a)
abbrev _root_.YangMills.DeltaSharedProofs.p501759 := @lintegral_stageStepDensity
include hS hM hf hfl hcut hcoin in
private theorem markedSampleLaw_isProbability (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β s n) := by
  induction s with
  | zero =>
    intro n _
    exact wilsonLaw_isProbability β n
  | succ s ih =>
    intro n _
    have := ih (n * ℓ.side)
    exact withDensity_prod_isProbabilityMeasure (μ := markedSampleLaw T β s (n * ℓ.side))
      (ρ := stepReferenceMeasure ℓ n) (w := stageStepDensity T s n)
      (measurable_stageStepDensity hS T hcoin s n) (lintegral_stageStepDensity hS hM hf hfl T hcut hcoin s n)
abbrev _root_.YangMills.SharedProofs.p20096 := @markedSampleLaw_isProbability
include hS hM hf hfl hcut hcoin in
private theorem measurePreserving_fst_markedSample (s n : ℕ) [NeZero n] :
    MeasurePreserving (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)
      (markedSampleLaw T β s (n * ℓ.side)) := by
  have := markedSampleLaw_isProbability hS hM hf hfl T hcut hcoin β s (n * ℓ.side)
  exact measurePreserving_fst_withDensity_prod (μ := markedSampleLaw T β s (n * ℓ.side))
    (ρ := stepReferenceMeasure ℓ n) (w := stageStepDensity T s n)
    (measurable_stageStepDensity hS T hcoin s n) (lintegral_stageStepDensity hS hM hf hfl T hcut hcoin s n)
abbrev _root_.YangMills.SharedProofs.p11229 := @measurePreserving_fst_markedSample
include hSc hf in
private theorem abs_sourceTerm_le (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (u : MarkedSample ℓ (s + 1) n) :
    |sourceTerm T al s n h u| ≤ ∑ c : TorusBond n, |bondSourceCoeff ℓ (al s) s h c| * 2 :=
  abs_stepSourceTerm_le (T.stage s).toStepSetup hSc hf (al s) s h _ _
private theorem response_succ_eq (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) :
    response T β al (s + 1) n h =
      (markedSampleLaw T β (s + 1) n)[stepSum T β al s n h | stageSigma T (s + 1) n] := by
  funext u
  rfl
include hS hM hSc hSt hf hfl hcut hcoin in
private theorem response_measurable_and_bounded (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)),
      Measurable (response T β al s n h) ∧
        ∃ C : ℝ, ∀ᵐ u ∂(markedSampleLaw T β s n), |response T β al s n h u| ≤ C := by
  induction s with
  | zero =>
    intro n _ h
    have hc : Continuous (curvatureObservable (m := n) h) := continuous_curvatureObservable h
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨hc.measurable, C, Filter.Eventually.of_forall fun W => ?_⟩
    have := hC W (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact this
  | succ s ih =>
    intro n _ h
    obtain ⟨hm, C, hC⟩ := ih (n * ℓ.side) h
    have hG : stageSigma T (s + 1) n ≤ markedSampleMeasurableSpace ℓ (s + 1) n :=
      (hSt ℓ hf T (s + 1) n).comap_le
    have hπ := measurePreserving_fst_markedSample hS hM hf hfl T hcut hcoin β s n
    rw [response_succ_eq]
    refine ⟨(stronglyMeasurable_condExp.mono hG).measurable, |C| +
      ∑ c : TorusBond n, |bondSourceCoeff ℓ (al s) s h c| * 2, ?_⟩
    have hnn : 0 ≤ |C| + ∑ c : TorusBond n, |bondSourceCoeff ℓ (al s) s h c| * 2 :=
      add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun c _ => by positivity)
    have hbπ : ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n), |response T β al s (n * ℓ.side) h u.1| ≤ C :=
      hπ.quasiMeasurePreserving.ae hC
    have hX : ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n), |stepSum T β al s n h u| ≤
        |C| + ∑ c : TorusBond n, |bondSourceCoeff ℓ (al s) s h c| * 2 := by
      filter_upwards [hbπ] with u hu
      have h2 := abs_sourceTerm_le hSc hf T al s n h u
      have h3 := abs_add_le (response T β al s (n * ℓ.side) h u.1) (sourceTerm T al s n h u)
      have h4 := le_abs_self C
      have h5 : |stepSum T β al s n h u| =
        |response T β al s (n * ℓ.side) h u.1 + sourceTerm T al s n h u| := rfl
      rw [h5]
      linarith
    exact ae_bdd_condExp_of_ae_bdd (m := stageSigma T (s + 1) n)
      (R := ⟨_, hnn⟩) (f := stepSum T β al s n h) (μ := markedSampleLaw T β (s + 1) n) hX
abbrev _root_.YangMills.SharedProofs.p50239 := @response_measurable_and_bounded
private theorem measurable_fst_markedSample (s n : ℕ) :
    Measurable fun u : MarkedSample ℓ (s + 1) n => u.1 := measurable_fst
abbrev _root_.YangMills.SharedProofs.p1941 := @measurable_fst_markedSample
private theorem measurable_sampleBelow (s : ℕ) : ∀ (d n : ℕ), Measurable (sampleBelow ℓ s d n)
  | 0, _ => measurable_id
  | d + 1, n => (measurable_sampleBelow s d (n * ℓ.side)).comp (measurable_fst_markedSample (s + d) n)
include hS hM hf hfl hcut hcoin in
private theorem map_sampleBelow (s : ℕ) : ∀ (d n : ℕ) [NeZero n],
    Measure.map (sampleBelow ℓ s d n) (markedSampleLaw T β (s + d) n) =
      markedSampleLaw T β s (fineSide ℓ.side d n)
  | 0, _, _ => Measure.map_id
  | d + 1, n, _ => by
    have h1 := map_sampleBelow s d (n * ℓ.side)
    have h2 := (measurePreserving_fst_markedSample hS hM hf hfl T hcut hcoin β (s + d) n).map_eq
    have h3 : Measure.map (sampleBelow ℓ s d (n * ℓ.side))
        (Measure.map (fun u : MarkedSample ℓ (s + d + 1) n => u.1) (markedSampleLaw T β (s + d + 1) n)) =
        Measure.map (sampleBelow ℓ s (d + 1) n) (markedSampleLaw T β (s + d + 1) n) :=
      Measure.map_map (measurable_sampleBelow s d (n * ℓ.side)) (measurable_fst_markedSample (s + d) n)
    rw [h2, h1] at h3
    exact h3.symm
end Chain
theorem sampleBelowLaw_holds (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hSc : BondScoreProperties) (hSt : StageStatesMeasurableStatement) :
    YangMills.Construction.ResponseInTheExpansion.sampleBelowLawStatement := by
  intro ℓ hf hfl T hcut hcoin β al
  refine ⟨fun s d n _ => ⟨measurable_sampleBelow s d n, map_sampleBelow hS hM hf hfl T hcut hcoin β s d n⟩,
    fun s n _ h => ?_⟩
  exact response_measurable_and_bounded hS hM hSc hSt hf hfl T hcut hcoin β al s n h
end YangMills.Construction.WeightedResponses
end
