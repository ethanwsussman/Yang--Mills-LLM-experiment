import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts BlockAverages
instance (L n : ℕ) : MeasurableSingletonClass (BaseChoice L n) := ⟨fun _ => trivial⟩
theorem measurable_finalField (p : StepParameters) : (s n : ℕ) → Measurable (finalField p s n)
  | 0, _ => measurable_id
  | s + 1, n => by
    letI := chainSampleMeasurableSpace p s (n * p.side)
    exact measurable_snd.comp measurable_snd
theorem isFiniteMeasure_chainReferenceMeasure (p : StepParameters) :
    (s n : ℕ) → [NeZero n] → IsFiniteMeasure (chainReferenceMeasure p s n)
  | 0, n, _ => inferInstanceAs (IsFiniteMeasure (fieldHaar n))
  | s + 1, n, _ => by
    letI := chainSampleMeasurableSpace p s (n * p.side)
    haveI := isFiniteMeasure_chainReferenceMeasure p s (n * p.side)
    haveI : IsFiniteMeasure (Measure.count : Measure (BaseChoice p.side n)) := inferInstance
    exact inferInstanceAs (IsFiniteMeasure ((chainReferenceMeasure p s (n * p.side)).prod
      ((Measure.count : Measure (BaseChoice p.side n)).prod (fieldHaar n))))
theorem continuous_wilsonWeight (β : ℝ) (n : ℕ) [NeZero n] : Continuous (wilsonWeight β n) := by
  have h : wilsonWeight β n = fun W => Real.exp (-β * TorusFields.wilsonAction Finset.univ W) := by
    funext W
    simp [wilsonWeight, NeZero.ne n]
  rw [h]
  exact Real.continuous_exp.comp (continuous_const.mul (TorusFields.continuous_wilsonAction _))
theorem measurable_stepTransitionDensity_sample (hS : StepTransitionDensityBounds) (p : StepParameters)
    (y : ℝ) (s n : ℕ) [NeZero n] :
    Measurable fun u : ChainSample p s (n * p.side) × BaseChoice p.side n × TorusField n =>
      stepTransitionDensity p y (finalField p s (n * p.side) u.1) u.2.1 u.2.2 := by
  classical
  have hsum : (fun u : ChainSample p s (n * p.side) × BaseChoice p.side n × TorusField n =>
      stepTransitionDensity p y (finalField p s (n * p.side) u.1) u.2.1 u.2.2) = fun u =>
      ∑ b : BaseChoice p.side n, if u.2.1 = b then
        stepTransitionDensity p y (finalField p s (n * p.side) u.1) b u.2.2 else 0 := by
    funext u
    simp
  rw [hsum]
  refine Finset.measurable_sum _ fun b _ => ?_
  have hset : MeasurableSet {u : ChainSample p s (n * p.side) × BaseChoice p.side n × TorusField n |
      u.2.1 = b} :=
    (measurable_fst.comp measurable_snd) (show MeasurableSet ({b} : Set (BaseChoice p.side n)) from trivial)
  have h1 : Measurable fun u : ChainSample p s (n * p.side) × BaseChoice p.side n × TorusField n =>
      (finalField p s (n * p.side) u.1, u.2.2) :=
    ((measurable_finalField p s (n * p.side)).comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have h2 := ((hS p y n).1 b).comp h1
  exact Measurable.ite hset h2 measurable_const
theorem measurable_chainJointDensity (hS : StepTransitionDensityBounds) (p : StepParameters) (β : ℝ)
    (x : ℕ → ℝ) : (s n : ℕ) → [NeZero n] → Measurable (chainJointDensity p β x s n)
  | 0, n, _ => (continuous_wilsonWeight β n).measurable.div_const _
  | s + 1, n, _ => by
    letI := chainSampleMeasurableSpace p s (n * p.side)
    exact ((measurable_chainJointDensity hS p β x s (n * p.side)).comp measurable_fst).mul
      (measurable_stepTransitionDensity_sample hS p (x s) s n)
theorem chainJointDensity_bounded (hS : StepTransitionDensityBounds) (p : StepParameters) (β : ℝ)
    (x : ℕ → ℝ) : (s n : ℕ) → [NeZero n] →
      ∃ C : ℝ, ∀ u, 0 ≤ chainJointDensity p β x s n u ∧ chainJointDensity p β x s n u ≤ C
  | 0, n, _ => by
    have hW : ∀ W, 0 ≤ wilsonWeight β n W := fun W => by
      simp only [wilsonWeight, NeZero.ne n, dite_false]
      exact (Real.exp_pos _).le
    have hZ : 0 ≤ ∫ W', wilsonWeight β n W' ∂(fieldHaar n) := integral_nonneg hW
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_wilsonWeight β n).continuousOn
    refine ⟨B / ∫ W', wilsonWeight β n W' ∂(fieldHaar n), fun W => ⟨div_nonneg (hW W) hZ, ?_⟩⟩
    have h1 := hB W (Set.mem_univ W)
    rw [Real.norm_eq_abs, abs_of_nonneg (hW W)] at h1
    exact div_le_div_of_nonneg_right h1 hZ
  | s + 1, n, _ => by
    obtain ⟨C, hC⟩ := chainJointDensity_bounded hS p β x s (n * p.side)
    obtain ⟨C', hC'⟩ := (hS p (x s) n).2
    refine ⟨C * C', fun u => ?_⟩
    have h1 := hC u.1
    have h2 := hC' (finalField p s (n * p.side) u.1) u.2.1 u.2.2
    exact ⟨mul_nonneg h1.1 h2.1, mul_le_mul h1.2 h2.2 h2.1 (h1.1.trans h1.2)⟩
theorem integral_chainJointLaw (hS : StepTransitionDensityBounds) (p : StepParameters) (β : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) [NeZero n] (g : ChainSample p s n → ℝ) :
    ∫ u, g u ∂(chainJointLaw p β x s n) =
      ∫ u, chainJointDensity p β x s n u * g u ∂(chainReferenceMeasure p s n) := by
  obtain ⟨C, hC⟩ := chainJointDensity_bounded hS p β x s n
  unfold chainJointLaw
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_chainJointDensity hS p β x s n).ennreal_ofReal
    (Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hC u).1]
theorem isFiniteMeasure_chainJointLaw (hS : StepTransitionDensityBounds) (p : StepParameters) (β : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) [NeZero n] : IsFiniteMeasure (chainJointLaw p β x s n) := by
  haveI := isFiniteMeasure_chainReferenceMeasure p s n
  obtain ⟨C, hC⟩ := chainJointDensity_bounded hS p β x s n
  unfold chainJointLaw
  refine isFiniteMeasure_withDensity ?_
  have hle : ∫⁻ u, ENNReal.ofReal (chainJointDensity p β x s n u) ∂(chainReferenceMeasure p s n) ≤
      ∫⁻ _, ENNReal.ofReal C ∂(chainReferenceMeasure p s n) :=
    lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hC u).2
  refine ne_of_lt (lt_of_le_of_lt hle ?_)
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
theorem integral_chainJointLaw_succ (hS : StepTransitionDensityBounds) (p : StepParameters) (β : ℝ)
    (x : ℕ → ℝ) (s n : ℕ) [NeZero n]
    (F : ChainSample p (s + 1) n → ℝ) (G : ChainSample p s (n * p.side) → ℝ) (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ u, |F u| ≤ C)
    (hG : ∀ u : ChainSample p s (n * p.side), ∑ b : BaseChoice p.side n, ∫ V : TorusField n,
      F (u, b, V) * stepTransitionDensity p (x s) (finalField p s (n * p.side) u) b V ∂(fieldHaar n) = G u) :
    ∫ u, F u ∂(chainJointLaw p β x (s + 1) n) = ∫ u, G u ∂(chainJointLaw p β x s (n * p.side)) := by
  letI := chainSampleMeasurableSpace p s (n * p.side)
  haveI := isFiniteMeasure_chainReferenceMeasure p s (n * p.side)
  obtain ⟨C, hC⟩ := chainJointDensity_bounded hS p β x s (n * p.side)
  obtain ⟨C', hC'⟩ := (hS p (x s) n).2
  obtain ⟨B, hB⟩ := hFb
  rw [integral_chainJointLaw hS, integral_chainJointLaw hS]
  set μ := chainReferenceMeasure p s (n * p.side) with hμ
  set ν : Measure (BaseChoice p.side n × TorusField n) :=
    (Measure.count : Measure (BaseChoice p.side n)).prod (fieldHaar n) with hν
  have hstep := measurable_stepTransitionDensity_sample hS p (x s) s n
  have hd := measurable_chainJointDensity hS p β x s (n * p.side)
  have hint : Integrable (fun u : ChainSample p s (n * p.side) × BaseChoice p.side n × TorusField n =>
      chainJointDensity p β x s (n * p.side) u.1 *
        stepTransitionDensity p (x s) (finalField p s (n * p.side) u.1) u.2.1 u.2.2 * F u) (μ.prod ν) := by
    refine Integrable.of_bound (((hd.comp measurable_fst).mul hstep).mul hF).aestronglyMeasurable
      (C * C' * B) (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hC u.1
    have h2 := hC' (finalField p s (n * p.side) u.1) u.2.1 u.2.2
    have h3 := hB u
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1.1, abs_of_nonneg h2.1]
    exact mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 (h1.1.trans h1.2)) h3 (abs_nonneg _)
      (mul_nonneg (h1.1.trans h1.2) (h2.1.trans h2.2))
  have hfirst : ∫ u, chainJointDensity p β x (s + 1) n u * F u ∂(chainReferenceMeasure p (s + 1) n) =
      ∫ u, ∫ q, chainJointDensity p β x s (n * p.side) u *
        stepTransitionDensity p (x s) (finalField p s (n * p.side) u) q.1 q.2 * F (u, q) ∂ν ∂μ :=
    integral_prod _ hint
  rw [hfirst]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ∫ q, chainJointDensity p β x s (n * p.side) u *
    stepTransitionDensity p (x s) (finalField p s (n * p.side) u) q.1 q.2 * F (u, q) ∂ν =
      chainJointDensity p β x s (n * p.side) u * G u
  rw [← hG u]
  have hsec : Measurable fun q : BaseChoice p.side n × TorusField n =>
      stepTransitionDensity p (x s) (finalField p s (n * p.side) u) q.1 q.2 * F (u, q) :=
    (hstep.comp measurable_prodMk_left).mul (hF.comp measurable_prodMk_left)
  have hisec : Integrable (fun q : BaseChoice p.side n × TorusField n =>
      stepTransitionDensity p (x s) (finalField p s (n * p.side) u) q.1 q.2 * F (u, q)) ν := by
    refine Integrable.of_bound hsec.aestronglyMeasurable (C' * B) (Filter.Eventually.of_forall fun q => ?_)
    have h2 := hC' (finalField p s (n * p.side) u) q.1 q.2
    have h3 := hB (u, q)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2.1]
    exact mul_le_mul h2.2 h3 (abs_nonneg _) (h2.1.trans h2.2)
  simp only [mul_assoc]
  rw [integral_const_mul, integral_prod _ hisec, integral_fintype hisec.integral_prod_left]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, smul_eq_mul, one_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  exact mul_comm _ _
theorem chainStepMean_holds (hS : StepTransitionDensityBounds) : ChainStepMean := fun p β x =>
  ⟨fun s n _ => isFiniteMeasure_chainJointLaw hS p β x s n, fun n _ g => integral_chainJointLaw hS p β x 0 n g,
    fun s n _ F G hF hFb hG => integral_chainJointLaw_succ hS p β x s n F G hF hFb hG⟩
end YangMills.Construction.WeightedResponses
end
