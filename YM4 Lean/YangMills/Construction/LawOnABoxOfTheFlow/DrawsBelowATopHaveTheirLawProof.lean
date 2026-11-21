import YangMills.Construction.ClusterExpansionOfAStep.TheMeanKernelHasMassOne
import YangMills.Construction.FreeEnergiesOfTheFlow.ThePastIsFreeGivenTheStateProof
import YangMills.Construction.LawOnABoxOfTheFlow.DrawsBelowATopHaveTheirLaw
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheCopiesAtNoLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxEvents
open TorusFields TorusLumps StepSettings StepCosts WeightedResponses BlockAverages ColdStepAtMirrorFrames RenormalizationStepParameters
section Abstract
private theorem map_fst_withDensity_of_lintegral_eq_one {A D : Type} [MeasurableSpace A] [MeasurableSpace D]
    {μ : Measure A} {ν : Measure D} [SFinite μ] [SFinite ν] {f : A × D → ENNReal} (hf : Measurable f)
    (hone : ∀ a, ∫⁻ d, f (a, d) ∂ν = 1) :
    ((μ.prod ν).withDensity f).map Prod.fst = μ := by
  ext B hB
  have hpre : MeasurableSet ((Prod.fst : A × D → A) ⁻¹' B) := measurable_fst hB
  have hset : (Prod.fst : A × D → A) ⁻¹' B = B ×ˢ Set.univ := by
    ext u
    simp
  rw [Measure.map_apply measurable_fst hB, withDensity_apply _ hpre, hset, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hf.aemeasurable]
  simp [hone]
end Abstract
section Marks
variable (S : StepSetup) {n : ℕ} [NeZero n]
private theorem markLaw_nonneg (hφ : IsCutoff S.ballRadius S.barrierFn) (W : TorusField (n * S.params.side))
    (V : TorusField n) (bad : Finset (TorusBond (n * S.params.side))) : 0 ≤ markLaw S W V bad := by apply _root_.YangMills.SharedProofs.p19776 <;> assumption
private theorem sum_markLaw_eq_one (W : TorusField (n * S.params.side)) (V : TorusField n) :
    ∑ bad : Finset (TorusBond (n * S.params.side)), markLaw S W V bad = 1 := by apply _root_.YangMills.SharedProofs.p2142 <;> assumption
end Marks
section Outcomes
variable {P : TorusLumps.StepParameters}
private instance (L n : ℕ) : DiscreteMeasurableSpace (BaseChoice L n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private theorem measurable_of_stepOutcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome P n → ℝ}
    (h : ∀ (b : BaseChoice P.side n) (bad : BondSet (n * P.side)),
      Measurable fun q : X × TorusField n => f (q.1, (b, q.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private instance (P : TorusLumps.StepParameters) (n : ℕ) [NeZero n] :
    IsFiniteMeasure (stepReferenceMeasure P n) := by
  unfold stepReferenceMeasure
  infer_instance
private theorem lintegral_stepReferenceMeasure {n : ℕ} [NeZero n] {g : StepOutcome P n → ENNReal}
    (hg : Measurable g) :
    ∫⁻ d, g d ∂(stepReferenceMeasure P n) =
      ∑ b : BaseChoice P.side n, ∫⁻ V : TorusField n, ∑ bad : BondSet (n * P.side), g (b, V, bad) ∂(fieldHaar n) := by
  unfold stepReferenceMeasure
  rw [lintegral_prod _ hg.aemeasurable, lintegral_count, tsum_fintype]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [lintegral_prod (fun y => g (b, y)) (hg.comp measurable_prodMk_left).aemeasurable]
  refine lintegral_congr fun V => ?_
  rw [lintegral_count, tsum_fintype]
end Outcomes
section OneStep
variable (S : StepSetup) {n : ℕ} [NeZero n]
private theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * S.params.side)),
      Measurable fun q : TorusField (n * S.params.side) × TorusField n => markLaw S q.1 q.2 bad) :
    Measurable fun q : TorusField (n * S.params.side) × StepOutcome S.params n => stepOutcomeDensity S q.1 q.2 :=
  measurable_of_stepOutcome fun b bad => ((hS S.params S.coupling n).1 b).mul (hB bad)
private theorem averagedKernel_eq_sum (W : TorusField (n * S.params.side)) (V : TorusField n) :
    averagedKernel S.params S.coupling (readAtLevel (stepBlockFrame S.params.side n) 0 W)
        (readAtLevel (stepBlockFrame S.params.side n) 1 V) =
      ∑ b : BaseChoice S.params.side n, stepTransitionDensity S.params S.coupling W b V := by
  classical
  unfold averagedKernel stepTransitionDensity
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
private theorem lintegral_stepOutcomeDensity_eq_one (hS : StepTransitionDensityBounds)
    (hK : AveragedKernelIntegralOne) (hP : S.params.Admissible)
    (hdepth : 11 * 2 ^ 12 * S.params.baseDepth < S.params.side) (hφ : IsCutoff S.ballRadius S.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * S.params.side)),
      Measurable fun q : TorusField (n * S.params.side) × TorusField n => markLaw S q.1 q.2 bad)
    (W : TorusField (n * S.params.side)) :
    ∫⁻ d, ENNReal.ofReal (stepOutcomeDensity S W d) ∂(stepReferenceMeasure S.params n) = 1 := by
  obtain ⟨C, hC⟩ := (hS S.params S.coupling n).2
  have hnn : ∀ (b : BaseChoice S.params.side n) (V : TorusField n),
      0 ≤ stepTransitionDensity S.params S.coupling W b V :=
    fun b V => (hC W b V).1
  have hm : Measurable fun d : StepOutcome S.params n => ENNReal.ofReal (stepOutcomeDensity S W d) :=
    ((measurable_stepOutcomeDensity S hS hB).comp measurable_prodMk_left).ennreal_ofReal
  have hbm : ∀ b : BaseChoice S.params.side n, Measurable fun V : TorusField n =>
      ENNReal.ofReal (stepTransitionDensity S.params S.coupling W b V) := fun b =>
    (((hS S.params S.coupling n).1 b).comp measurable_prodMk_left).ennreal_ofReal
  have hsumBad : ∀ (b : BaseChoice S.params.side n) (V : TorusField n),
      ∑ bad : BondSet (n * S.params.side), ENNReal.ofReal (stepOutcomeDensity S W (b, V, bad)) =
        ENNReal.ofReal (stepTransitionDensity S.params S.coupling W b V) := by
    intro b V
    have hof : ∑ bad : BondSet (n * S.params.side), ENNReal.ofReal (stepOutcomeDensity S W (b, V, bad)) =
        ENNReal.ofReal (∑ bad : BondSet (n * S.params.side), stepOutcomeDensity S W (b, V, bad)) :=
      (ENNReal.ofReal_sum_of_nonneg fun bad _ => mul_nonneg (hnn b V) (markLaw_nonneg S hφ W V bad)).symm
    have hone : ∑ bad : BondSet (n * S.params.side), markLaw S W V bad = 1 := sum_markLaw_eq_one S W V
    have hdef : ∀ bad : BondSet (n * S.params.side), stepOutcomeDensity S W (b, V, bad) =
        stepTransitionDensity S.params S.coupling W b V * markLaw S W V bad := fun _ => rfl
    have hsum : ∑ bad : BondSet (n * S.params.side), stepOutcomeDensity S W (b, V, bad) =
        stepTransitionDensity S.params S.coupling W b V := by
      simp only [hdef]
      exact (Finset.mul_sum _ _ _).symm.trans (by rw [hone, mul_one])
    rw [hof, hsum]
  have hsumBase : ∀ V : TorusField n,
      ∑ b : BaseChoice S.params.side n, ENNReal.ofReal (stepTransitionDensity S.params S.coupling W b V) =
      ENNReal.ofReal (averagedKernel S.params S.coupling (readAtLevel (stepBlockFrame S.params.side n) 0 W)
        (readAtLevel (stepBlockFrame S.params.side n) 1 V)) := by
    intro V
    rw [averagedKernel_eq_sum, ENNReal.ofReal_sum_of_nonneg fun b _ => hnn b V]
  have hint := hK S.params hP hdepth S.coupling n (readAtLevel (stepBlockFrame S.params.side n) 0 W)
  have hI : Integrable (fun V : TorusField n =>
      averagedKernel S.params S.coupling (readAtLevel (stepBlockFrame S.params.side n) 0 W)
        (readAtLevel (stepBlockFrame S.params.side n) 1 V)) (fieldHaar n) := by
    by_contra hni
    rw [integral_undef hni] at hint
    exact zero_ne_one hint
  have h0 : 0 ≤ᵐ[fieldHaar n] fun V : TorusField n =>
      averagedKernel S.params S.coupling (readAtLevel (stepBlockFrame S.params.side n) 0 W)
        (readAtLevel (stepBlockFrame S.params.side n) 1 V) :=
    Filter.Eventually.of_forall fun V => by
      show 0 ≤ averagedKernel _ _ _ _
      rw [averagedKernel_eq_sum]
      exact Finset.sum_nonneg fun b _ => hnn b V
  rw [lintegral_stepReferenceMeasure hm]
  simp only [hsumBad]
  rw [← lintegral_finsetSum _ fun b _ => hbm b]
  simp only [hsumBase]
  rw [← ofReal_integral_eq_lintegral_ofReal hI h0, hint, ENNReal.ofReal_one]
end OneStep
section Tower
variable {P : TorusLumps.StepParameters}
private theorem measurable_topField : (s n : ℕ) → Measurable (topField P s n)
  | 0, _ => measurable_id
  | _ + 1, _ => measurable_fst.comp (measurable_snd.comp measurable_snd)
private theorem stage_isCutoff (T : StageTower P) (h : IsCutoff (P.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
private theorem isProbabilityMeasure_wilsonLaw (β : ℝ) (m : ℕ) [NeZero m] : IsProbabilityMeasure (wilsonLaw β m) := by apply _root_.YangMills.SharedProofs.p1521 <;> assumption
private theorem measurable_sampleBelow (k : ℕ) : (d n : ℕ) → Measurable (ResponseInTheExpansion.sampleBelow P k d n)
  | 0, _ => measurable_id
  | d + 1, n => (measurable_sampleBelow k d (n * P.side)).comp measurable_fst
variable (hS : StepTransitionDensityBounds) (hK : AveragedKernelIntegralOne)
  (hP : P.Admissible) (hdepth : 11 * 2 ^ 12 * P.baseDepth < P.side) (T : StageTower P)
  (hφ : IsCutoff (P.threshold / 64) T.base.barrierFn) (hmark : T.MarksMeasurable) (β : ℝ)
private def stepKernel (s n : ℕ) [NeZero n] (u : MarkedSample P s (n * P.side) × StepOutcome P n) : ENNReal :=
  ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField P s (n * P.side) u.1) u.2)
include hS hmark in
private theorem measurable_stepKernel (s n : ℕ) [NeZero n] : Measurable (stepKernel T s n) := by
  have h1 := measurable_stepOutcomeDensity (T.stage s).toStepSetup (n := n) hS (fun bad => hmark s n bad)
  have h2 : Measurable fun u : MarkedSample P s (n * P.side) × StepOutcome P n =>
      ((topField P s (n * P.side) u.1, u.2) : TorusField (n * P.side) × StepOutcome P n) :=
    ((measurable_topField s (n * P.side)).comp measurable_fst).prodMk measurable_snd
  exact (h1.comp h2).ennreal_ofReal
include hS hK hP hdepth hφ hmark in
private theorem lintegral_stepKernel_eq_one (s n : ℕ) [NeZero n] (a : MarkedSample P s (n * P.side)) :
    ∫⁻ d, stepKernel T s n (a, d) ∂(stepReferenceMeasure P n) = 1 :=
  lintegral_stepOutcomeDensity_eq_one (T.stage s).toStepSetup hS hK hP hdepth (stage_isCutoff T hφ s)
    (fun bad => hmark s n bad) (topField P s (n * P.side) a)
private def dropLastStep (s n : ℕ) : MarkedSample P (s + 1) n → MarkedSample P s (n * P.side) := fun u => u.1
private theorem measurable_dropLastStep (s n : ℕ) : Measurable (dropLastStep (P := P) s n) :=
  measurable_fst
include hS hK hP hdepth hφ hmark in
private theorem map_dropLastStep (s n : ℕ) [NeZero n] [IsProbabilityMeasure (markedSampleLaw T β s (n * P.side))] :
    (markedSampleLaw T β (s + 1) n).map (dropLastStep s n) = markedSampleLaw T β s (n * P.side) :=
  map_fst_withDensity_of_lintegral_eq_one (μ := markedSampleLaw T β s (n * P.side)) (ν := stepReferenceMeasure P n)
    (f := stepKernel T s n) (measurable_stepKernel hS T hmark s n)
    (lintegral_stepKernel_eq_one hS hK hP hdepth T hφ hmark s n)
include hS hK hP hdepth hφ hmark in
private theorem isProbabilityMeasure_markedSampleLaw (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β s n) := by
  induction s with
  | zero =>
    intro n _
    exact isProbabilityMeasure_wilsonLaw β n
  | succ s ih =>
    intro n _
    have := ih (n * P.side)
    have hmap := map_dropLastStep hS hK hP hdepth T hφ hmark β s n
    constructor
    have h1 : (markedSampleLaw T β (s + 1) n).map (dropLastStep s n) Set.univ = 1 := by
      rw [hmap]
      exact measure_univ
    rwa [Measure.map_apply (measurable_dropLastStep s n) MeasurableSet.univ, Set.preimage_univ] at h1
include hS hK hP hdepth hφ hmark in
private theorem map_sampleBelow (k d : ℕ) : ∀ (n : ℕ) [NeZero n],
    (markedSampleLaw T β (k + d) n).map (ResponseInTheExpansion.sampleBelow P k d n) =
      markedSampleLaw T β k (fineSide P.side d n) := by
  induction d with
  | zero =>
    intro n _
    exact Measure.map_id
  | succ d ih =>
    intro n _
    have := isProbabilityMeasure_markedSampleLaw hS hK hP hdepth T hφ hmark β (k + d) (n * P.side)
    have hmap := map_dropLastStep hS hK hP hdepth T hφ hmark β (k + d) n
    have hcomp := Measure.map_map (μ := markedSampleLaw T β (k + d + 1) n) (measurable_sampleBelow k d (n * P.side))
      (measurable_dropLastStep (k + d) n)
    exact hcomp.symm.trans
      ((congrArg (Measure.map (ResponseInTheExpansion.sampleBelow P k d (n * P.side))) hmap).trans (ih (n * P.side)))
end Tower
theorem sampleBelowLaw_holds (hS : StepTransitionDensityBounds) (hK : AveragedKernelIntegralOne) :
    sampleBelowLawStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, fun L _ _ Tb _ _ hD _ => ⟨Tb.floorMin, fun y hy _ _ T β k s n _ hst hmk _ => ?_⟩⟩
  have hP : (Tb.stepParameters y).Admissible := hD.fits y hy
  have hdepth : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hP.depth_lt
  have hφ : IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have hb : T.base.barrierFn = Tb.cutoff := (hst.onFamily 0 (Nat.zero_le _)).barrierFn_eq
    rw [hb]
    exact hD.cut
  exact ⟨isProbabilityMeasure_markedSampleLaw hS hK hP hdepth T hφ hmk β (k + s) n,
    map_sampleBelow hS hK hP hdepth T hφ hmk β k s n⟩
end YangMills.Construction.BoxEvents
end
