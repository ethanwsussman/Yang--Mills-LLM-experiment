import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.FormsOnATorus.LawOfTheTopIsTheChainMean
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusLumps TorusFields StepCosts BlockAverages
variable {p : StepParameters}
private theorem measurable_finalField_aux (p : StepParameters) :
    (s n : ℕ) → Measurable (finalField p s n)
  | 0, _ => measurable_id
  | s + 1, n => by
    letI := chainSampleMeasurableSpace p s (n * p.side)
    exact measurable_snd.comp measurable_snd
open Classical in
private theorem sum_stepTransitionDensity_eq (x : ℝ) {n : ℕ} [NeZero n]
    (U : TorusField (n * p.side)) (V : TorusField n) :
    ∑ b : BaseChoice p.side n, stepTransitionDensity p x U b V =
      averagedKernel p x (fineLevelField p n U) (coarseLevelField p n V) := by
  unfold stepTransitionDensity averagedKernel
  rw [Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
private theorem toReal_le_one_of_le {a : ENNReal} (h : a ≤ 1) : a.toReal ≤ 1 := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using this
private theorem sum_integral_stepTransitionDensity (hDens : StepTransitionDensityBounds)
    (hKer : BondKernelProperties) (hBor : BondKernelBorel) (x : ℝ) {n : ℕ} [NeZero n]
    {f : TorusField n → ENNReal} (hf : Measurable f)
    (hf1 : ∀ V, f V ≤ 1) (U : TorusField (n * p.side)) :
    ∑ b : BaseChoice p.side n, ∫ V : TorusField n, (f V).toReal * stepTransitionDensity p x U b V ∂(fieldHaar n) =
      (stepExpectation p x f U).toReal := by
  classical
  have hint : ∀ b : BaseChoice p.side n,
      Integrable (fun V : TorusField n => (f V).toReal * stepTransitionDensity p x U b V) (fieldHaar n) := by
    intro b
    obtain ⟨C, hC⟩ := (hDens p x n).2
    have hpair : Measurable fun V : TorusField n => ((U, V) : TorusField (n * p.side) × TorusField n) :=
      measurable_prodMk_left
    have hcomp := ((hDens p x n).1 b).comp hpair
    have hmeas : Measurable fun V : TorusField n => stepTransitionDensity p x U b V := hcomp
    refine Integrable.of_bound (hf.ennreal_toReal.mul hmeas).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun V => ?_)
    have hbd := hC U b V
    have hle : (f V).toReal ≤ 1 := toReal_le_one_of_le (hf1 V)
    have hnn : 0 ≤ (f V).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn hbd.1)]
    nlinarith [hbd.1, hbd.2]
  rw [← integral_finset_sum _ fun b _ => hint b]
  have hmeas : Measurable fun V : TorusField n =>
      ENNReal.ofReal (averagedKernel p x (fineLevelField p n U) (coarseLevelField p n V)) * f V :=
    (measurable_averagedKernel_right hBor x U).ennreal_ofReal.mul hf
  unfold stepExpectation
  rw [← integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall fun V =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((hf1 V).trans_lt ENNReal.one_lt_top))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  show ∑ b : BaseChoice p.side n, (f V).toReal * stepTransitionDensity p x U b V = _
  show _ = (ENNReal.ofReal (averagedKernel p x (fineLevelField p n U) (coarseLevelField p n V)) * f V).toReal
  rw [← Finset.mul_sum, sum_stepTransitionDensity_eq, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (averagedKernel_nonneg hKer x _ _), mul_comm]
theorem finalFieldLawIsChainExpectation_holds (hMean : ChainStepMean)
    (hDens : StepTransitionDensityBounds) (hKer : BondKernelProperties) (hBor : BondKernelBorel)
    (hMass : AveragedKernelIntegralOne) :
    FinalFieldLawIsChainExpectation := by
  intro p hfit hside β x s
  induction s with
  | zero =>
    intro n _ f hf hf1
    refine ⟨hf, hf1, ?_⟩
    have hbase := (hMean p β x).2.1 n (fun U => (f U).toReal)
    show ∫ U, (f U).toReal ∂(chainJointLaw p β x 0 n) = ∫ U, (f U).toReal ∂(wilsonLaw β n)
    rw [hbase]
    have hcont : Continuous fun U : TorusField n => Real.exp (-β * wilsonAction Finset.univ U) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction _))
    have hweight : ∀ U : TorusField n, wilsonWeight β n U = Real.exp (-β * wilsonAction Finset.univ U) :=
      fun U => by
        simp [wilsonWeight, NeZero.ne n]
    simp only [hweight]
    set Z := ∫ U' : TorusField n, Real.exp (-β * wilsonAction Finset.univ U') ∂(fieldHaar n) with hZ
    have hZ0 : 0 ≤ Z := integral_nonneg fun U => (Real.exp_pos _).le
    unfold wilsonLaw
    rw [integral_withDensity_eq_integral_toReal_smul (hcont.measurable.div_const _).ennreal_ofReal
      (Filter.Eventually.of_forall fun U => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ0)]
  | succ s ih =>
    intro n _ f hf hf1
    have hm : Measurable (stepExpectation p (x s) f) := measurable_stepExpectation hBor (x s) hf
    have hle := stepExpectation_le_one hKer hMass hfit hside (x s) hf1
    obtain ⟨h1, h2, h3⟩ := ih (n * p.side) (stepExpectation p (x s) f) hm hle
    refine ⟨h1, h2, Eq.trans ?_ h3⟩
    refine (hMean p β x).2.2 s n (fun u => (f (finalField p (s + 1) n u)).toReal)
      (fun u => (stepExpectation p (x s) f (finalField p s (n * p.side) u)).toReal)
      (hf.comp (measurable_finalField_aux p (s + 1) n)).ennreal_toReal ⟨1, fun u => ?_⟩ fun u => ?_
    · rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact toReal_le_one_of_le (hf1 _)
    · exact sum_integral_stepTransitionDensity hDens hKer hBor (x s) hf hf1 _
end YangMills.Construction.WeightedResponses
end
