import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongASegmentOfLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.DensityMeans
namespace Segment
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} {S : Set Ω} {Ψ₀ Ψ₁ : Ω → ℝ} {M : ℝ}
def segmentExpWeight (Ψ₀ Ψ₁ : Ω → ℝ) (v : ℝ) (ω : Ω) : ℝ := Real.exp (-(segmentPoint Ψ₀ Ψ₁ v ω))
theorem aestronglyMeasurable_segmentExpWeight (h0 : AEStronglyMeasurable Ψ₀ ν)
    (h1 : AEStronglyMeasurable Ψ₁ ν) (v : ℝ) :
    AEStronglyMeasurable (segmentExpWeight Ψ₀ Ψ₁ v) ν := by
  have hs : AEStronglyMeasurable (segmentPoint Ψ₀ Ψ₁ v) ν :=
    (h1.const_mul v).add (h0.const_mul (1 - v))
  exact Real.continuous_exp.comp_aestronglyMeasurable hs.neg
omit [MeasurableSpace Ω] in
theorem abs_segmentPoint_le {ω : Ω} (hM0 : |Ψ₀ ω| ≤ M) (hM1 : |Ψ₁ ω| ≤ M) (v₀ v : ℝ)
    (hv : |v - v₀| < 1) :
    |segmentPoint Ψ₀ Ψ₁ v ω| ≤ (2 * |v₀| + 4) * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hM0
  have h1 : |v| ≤ |v₀| + 1 := by
    have := abs_sub_abs_le_abs_sub v v₀
    linarith
  have h2 : |1 - v| ≤ |v₀| + 2 := by
    have := abs_sub 1 v
    simp only [abs_one] at this
    linarith
  unfold segmentPoint
  calc |v * Ψ₁ ω + (1 - v) * Ψ₀ ω| ≤ |v * Ψ₁ ω| + |(1 - v) * Ψ₀ ω| := abs_add_le _ _
    _ = |v| * |Ψ₁ ω| + |1 - v| * |Ψ₀ ω| := by rw [abs_mul, abs_mul]
    _ ≤ (|v₀| + 1) * M + (|v₀| + 2) * M := by gcongr
    _ ≤ (2 * |v₀| + 4) * M := by nlinarith
omit [MeasurableSpace Ω] in
theorem abs_segmentExpWeight_le {ω : Ω} (hM0 : |Ψ₀ ω| ≤ M) (hM1 : |Ψ₁ ω| ≤ M) (v₀ v : ℝ)
    (hv : |v - v₀| < 1) :
    |segmentExpWeight Ψ₀ Ψ₁ v ω| ≤ Real.exp ((2 * |v₀| + 4) * M) := by
  unfold segmentExpWeight
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have := abs_segmentPoint_le hM0 hM1 v₀ v hv
  have := neg_abs_le (segmentPoint Ψ₀ Ψ₁ v ω)
  linarith [neg_le_abs (segmentPoint Ψ₀ Ψ₁ v ω)]
omit [MeasurableSpace Ω] in
theorem exp_neg_le_segmentExpWeight {ω : Ω} (hM0 : |Ψ₀ ω| ≤ M) (hM1 : |Ψ₁ ω| ≤ M) (v₀ : ℝ) :
    Real.exp (-((2 * |v₀| + 4) * M)) ≤ segmentExpWeight Ψ₀ Ψ₁ v₀ ω := by
  unfold segmentExpWeight
  apply Real.exp_le_exp.mpr
  have := abs_segmentPoint_le hM0 hM1 v₀ v₀ (by simp)
  have := le_abs_self (segmentPoint Ψ₀ Ψ₁ v₀ ω)
  linarith
theorem ae_restrict_of_forall_mem (hS : MeasurableSet S) {P : Ω → Prop} (h : ∀ ω ∈ S, P ω)
    {μ : Measure Ω} :
    ∀ᵐ ω ∂(μ.restrict S), P ω :=
  (ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall h)
theorem integrable_mul_segmentExpWeight {μ : Measure Ω} (hS : MeasurableSet S)
    (h0 : AEStronglyMeasurable Ψ₀ (μ.restrict S)) (h1 : AEStronglyMeasurable Ψ₁ (μ.restrict S))
    (hM0 : ∀ ω ∈ S, |Ψ₀ ω| ≤ M) (hM1 : ∀ ω ∈ S, |Ψ₁ ω| ≤ M) {g : Ω → ℝ}
    (hg : Integrable g (μ.restrict S)) (v : ℝ) :
    Integrable (fun ω => g ω * segmentExpWeight Ψ₀ Ψ₁ v ω) (μ.restrict S) := by
  refine hg.mul_bdd (c := Real.exp ((2 * |v| + 4) * M))
    (aestronglyMeasurable_segmentExpWeight h0 h1 v) ?_
  refine ae_restrict_of_forall_mem hS fun ω hω => ?_
  simpa using abs_segmentExpWeight_le (hM0 ω hω) (hM1 ω hω) v v (by simp)
theorem hasDerivAt_integral_mul_segmentExpWeight {μ : Measure Ω} (hS : MeasurableSet S)
    (h0 : AEStronglyMeasurable Ψ₀ (μ.restrict S)) (h1 : AEStronglyMeasurable Ψ₁ (μ.restrict S))
    (hM0 : ∀ ω ∈ S, |Ψ₀ ω| ≤ M) (hM1 : ∀ ω ∈ S, |Ψ₁ ω| ≤ M) {g : Ω → ℝ}
    (hg : Integrable g (μ.restrict S)) (v₀ : ℝ) :
    HasDerivAt (fun v => ∫ ω, g ω * segmentExpWeight Ψ₀ Ψ₁ v ω ∂(μ.restrict S))
      (∫ ω, -(g ω * (Ψ₁ ω - Ψ₀ ω) * segmentExpWeight Ψ₀ Ψ₁ v₀ ω) ∂(μ.restrict S)) v₀ := by
  set K : ℝ := Real.exp ((2 * |v₀| + 4) * M) with hK
  have hD : AEStronglyMeasurable (fun ω => Ψ₁ ω - Ψ₀ ω) (μ.restrict S) := h1.sub h0
  have hM : ∀ ω ∈ S, 0 ≤ M := fun ω hω => (abs_nonneg _).trans (hM0 ω hω)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict S) (x₀ := v₀)
    (s := Metric.ball v₀ 1) (F := fun v ω => g ω * segmentExpWeight Ψ₀ Ψ₁ v ω)
    (F' := fun v ω => -(g ω * (Ψ₁ ω - Ψ₀ ω) * segmentExpWeight Ψ₀ Ψ₁ v ω))
    (bound := fun ω => |g ω| * (2 * M) * K)
    (Metric.ball_mem_nhds v₀ one_pos)
    (Filter.Eventually.of_forall fun v =>
      hg.aestronglyMeasurable.mul (aestronglyMeasurable_segmentExpWeight h0 h1 v))
    (integrable_mul_segmentExpWeight hS h0 h1 hM0 hM1 hg v₀)
    (((hg.aestronglyMeasurable.mul hD).mul (aestronglyMeasurable_segmentExpWeight h0 h1 v₀)).neg)
    (ae_restrict_of_forall_mem hS fun ω hω v hv => ?_)
    ((hg.abs.mul_const (2 * M)).mul_const K)
    (Filter.Eventually.of_forall fun ω v _ => ?_)
  · exact key.2
  · have hv' : |v - v₀| < 1 := by simpa [Real.dist_eq] using hv
    rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul]
    have hd : |Ψ₁ ω - Ψ₀ ω| ≤ 2 * M := by
      have := abs_sub (Ψ₁ ω) (Ψ₀ ω)
      have e1 := hM0 ω hω
      have e2 := hM1 ω hω
      linarith
    exact mul_le_mul (mul_le_mul le_rfl hd (abs_nonneg _) (abs_nonneg _))
      (abs_segmentExpWeight_le (hM0 ω hω) (hM1 ω hω) v₀ v hv') (abs_nonneg _)
      (by have := hM ω hω; positivity)
  · unfold segmentExpWeight segmentPoint
    have h1' : HasDerivAt (fun y : ℝ => -(y * Ψ₁ ω + (1 - y) * Ψ₀ ω)) (-(Ψ₁ ω - Ψ₀ ω)) v := by
      have e1 : HasDerivAt (fun y : ℝ => y * Ψ₁ ω) (Ψ₁ ω) v := by
        simpa using (hasDerivAt_id v).mul_const (Ψ₁ ω)
      have e2 : HasDerivAt (fun y : ℝ => (1 - y) * Ψ₀ ω) (-(Ψ₀ ω)) v := by
        have h0' : HasDerivAt (fun y : ℝ => 1 - y) (-1) v := by
          simpa using (hasDerivAt_id v).const_sub 1
        exact HasDerivAt.congr_deriv (h0'.mul_const (Ψ₀ ω)) (by ring)
      exact HasDerivAt.congr_deriv (e1.add e2).neg (by ring)
    have h2 := (h1'.exp).const_mul (g ω)
    exact HasDerivAt.congr_deriv h2 (by ring)
theorem integral_eq_setIntegral_of_eq_zero_off {μ : Measure Ω} (_hS : MeasurableSet S)
    {f : Ω → ℝ} (hf : ∀ ω, ω ∉ S → f ω = 0) :
    ∫ ω, f ω ∂μ = ∫ ω, f ω ∂(μ.restrict S) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm
end Segment
open Segment in
theorem weightedMean_diff_le_of_deriv_bound : WeightedMeanDiffLeOfDerivBound := by
  intro Ω _ μ S w Ψ₀ Ψ₁ A₀ A₁ M B hS hw0 hwS hwi hwp h0 h1 hM0 hM1 hA0 hA1 hB
  set ν := μ.restrict S with hν
  have hwiν : Integrable w ν := hwi.restrict
  have hA0ν : Integrable (fun ω => A₀ ω * w ω) ν := hA0.restrict
  have hA1ν : Integrable (fun ω => A₁ ω * w ω) ν := hA1.restrict
  set Z : ℝ → ℝ := fun v => ∫ ω, w ω * segmentExpWeight Ψ₀ Ψ₁ v ω ∂ν with hZ
  set G₀ : ℝ → ℝ := fun v => ∫ ω, (A₀ ω * w ω) * segmentExpWeight Ψ₀ Ψ₁ v ω ∂ν with hG₀
  set G₁ : ℝ → ℝ := fun v => ∫ ω, (A₁ ω * w ω) * segmentExpWeight Ψ₀ Ψ₁ v ω ∂ν with hG₁
  set Z' : ℝ → ℝ := fun v =>
    ∫ ω, -(w ω * (Ψ₁ ω - Ψ₀ ω) * segmentExpWeight Ψ₀ Ψ₁ v ω) ∂ν with hZ'
  set G₀' : ℝ → ℝ := fun v =>
    ∫ ω, -((A₀ ω * w ω) * (Ψ₁ ω - Ψ₀ ω) * segmentExpWeight Ψ₀ Ψ₁ v ω) ∂ν with hG₀'
  set G₁' : ℝ → ℝ := fun v =>
    ∫ ω, -((A₁ ω * w ω) * (Ψ₁ ω - Ψ₀ ω) * segmentExpWeight Ψ₀ Ψ₁ v ω) ∂ν with hG₁'
  have dZ : ∀ v, HasDerivAt Z (Z' v) v := fun v =>
    hasDerivAt_integral_mul_segmentExpWeight hS h0 h1 hM0 hM1 hwiν v
  have dG₀ : ∀ v, HasDerivAt G₀ (G₀' v) v := fun v =>
    hasDerivAt_integral_mul_segmentExpWeight hS h0 h1 hM0 hM1 hA0ν v
  have dG₁ : ∀ v, HasDerivAt G₁ (G₁' v) v := fun v =>
    hasDerivAt_integral_mul_segmentExpWeight hS h0 h1 hM0 hM1 hA1ν v
  have hwν : (0 : ℝ) < ∫ ω, w ω ∂ν := by
    rw [hν, ← integral_eq_setIntegral_of_eq_zero_off hS hwS]
    exact hwp
  have hZpos : ∀ v, 0 < Z v := by
    intro v
    set c : ℝ := Real.exp (-((2 * |v| + 4) * M)) with hc
    have hcpos : 0 < c := Real.exp_pos _
    have hle : ∫ ω, c * w ω ∂ν ≤ Z v := by
      refine integral_mono_ae (hwiν.const_mul c)
        (integrable_mul_segmentExpWeight hS h0 h1 hM0 hM1 hwiν v) ?_
      refine Segment.ae_restrict_of_forall_mem hS fun ω hω => ?_
      have := exp_neg_le_segmentExpWeight (hM0 ω hω) (hM1 ω hω) v
      have h3 := mul_le_mul_of_nonneg_left this (hw0 ω)
      show c * w ω ≤ w ω * segmentExpWeight Ψ₀ Ψ₁ v ω
      rw [mul_comm]
      exact h3
    rw [integral_const_mul] at hle
    exact lt_of_lt_of_le (mul_pos hcpos hwν) hle
  set N : ℝ → ℝ := fun v => v * G₁ v + (1 - v) * G₀ v with hN
  have dN : ∀ v, HasDerivAt N (G₁ v - G₀ v + (v * G₁' v + (1 - v) * G₀' v)) v := by
    intro v
    have e1 := (hasDerivAt_id v).mul (dG₁ v)
    have e2 := ((hasDerivAt_id v).const_sub 1).mul (dG₀ v)
    refine HasDerivAt.congr_deriv (e1.add e2) ?_
    simp only [id]
    ring
  have dm : ∀ v, HasDerivAt (fun v => N v / Z v)
      (((G₁ v - G₀ v + (v * G₁' v + (1 - v) * G₀' v)) * Z v - N v * Z' v) / Z v ^ 2) v :=
    fun v => (dN v).div (dZ v) (hZpos v).ne'
  have hmean : ∀ (v : ℝ) (H : Ω → ℝ),
      weightedMean μ w (segmentPoint Ψ₀ Ψ₁ v) H =
        (∫ ω, H ω * (w ω * segmentExpWeight Ψ₀ Ψ₁ v ω) ∂ν) / Z v := by
    intro v H
    have e1 : ∫ ω, H ω * (w ω * Real.exp (-(segmentPoint Ψ₀ Ψ₁ v ω))) ∂μ =
        ∫ ω, H ω * (w ω * segmentExpWeight Ψ₀ Ψ₁ v ω) ∂ν := by
      refine integral_eq_setIntegral_of_eq_zero_off hS fun ω hω => ?_
      rw [hwS ω hω]; ring
    have e2 : ∫ ω, w ω * Real.exp (-(segmentPoint Ψ₀ Ψ₁ v ω)) ∂μ = Z v := by
      refine integral_eq_setIntegral_of_eq_zero_off hS fun ω hω => ?_
      rw [hwS ω hω]; ring
    unfold weightedMean
    rw [e1, e2]
  have hi0 : ∀ v, Integrable (fun ω => (A₀ ω * w ω) * segmentExpWeight Ψ₀ Ψ₁ v ω) ν :=
    fun v => integrable_mul_segmentExpWeight hS h0 h1 hM0 hM1 hA0ν v
  have hi1 : ∀ v, Integrable (fun ω => (A₁ ω * w ω) * segmentExpWeight Ψ₀ Ψ₁ v ω) ν :=
    fun v => integrable_mul_segmentExpWeight hS h0 h1 hM0 hM1 hA1ν v
  have hdm : AEStronglyMeasurable (fun ω => Ψ₁ ω - Ψ₀ ω) ν := h1.sub h0
  have hbdD : ∀ᵐ ω ∂ν, ‖Ψ₁ ω - Ψ₀ ω‖ ≤ 2 * M := by
    refine Segment.ae_restrict_of_forall_mem hS fun ω hω => ?_
    rw [Real.norm_eq_abs]
    have := abs_sub (Ψ₁ ω) (Ψ₀ ω)
    have e1 := hM0 ω hω
    have e2 := hM1 ω hω
    linarith
  have hj : ∀ (g : Ω → ℝ), Integrable g ν →
      Integrable (fun ω => g ω * (Ψ₁ ω - Ψ₀ ω)) ν := fun g hg => hg.mul_bdd hdm hbdD
  have hj0 : ∀ v, Integrable
      (fun ω => (A₀ ω * w ω) * (Ψ₁ ω - Ψ₀ ω) * segmentExpWeight Ψ₀ Ψ₁ v ω) ν :=
    fun v => integrable_mul_segmentExpWeight hS h0 h1 hM0 hM1 (hj _ hA0ν) v
  have hj1 : ∀ v, Integrable
      (fun ω => (A₁ ω * w ω) * (Ψ₁ ω - Ψ₀ ω) * segmentExpWeight Ψ₀ Ψ₁ v ω) ν :=
    fun v => integrable_mul_segmentExpWeight hS h0 h1 hM0 hM1 (hj _ hA1ν) v
  have hslope : ∀ v, meanDerivAlongSegment μ w Ψ₀ Ψ₁ A₀ A₁ v =
      ((G₁ v - G₀ v + (v * G₁' v + (1 - v) * G₀' v)) * Z v - N v * Z' v) / Z v ^ 2 := by
    intro v
    have a1 : ∫ ω, (A₁ ω - A₀ ω) * (w ω * segmentExpWeight Ψ₀ Ψ₁ v ω) ∂ν = G₁ v - G₀ v := by
      simp only [hG₀, hG₁]
      rw [← integral_sub (hi1 v) (hi0 v)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
    have a2 : ∫ ω, (segmentPoint A₀ A₁ v ω * (Ψ₁ ω - Ψ₀ ω)) *
        (w ω * segmentExpWeight Ψ₀ Ψ₁ v ω) ∂ν = -(v * G₁' v + (1 - v) * G₀' v) := by
      simp only [hG₀', hG₁']
      rw [integral_neg, integral_neg, mul_neg, mul_neg, ← neg_add, neg_neg, ← integral_const_mul,
        ← integral_const_mul, ← integral_add ((hj1 v).const_mul v) ((hj0 v).const_mul (1 - v))]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        simp only [segmentPoint]; ring)
    have a3 : ∫ ω, segmentPoint A₀ A₁ v ω * (w ω * segmentExpWeight Ψ₀ Ψ₁ v ω) ∂ν = N v := by
      simp only [hN, hG₀, hG₁]
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add ((hi1 v).const_mul v) ((hi0 v).const_mul (1 - v))]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        simp only [segmentPoint]; ring)
    have a4 : ∫ ω, (Ψ₁ ω - Ψ₀ ω) * (w ω * segmentExpWeight Ψ₀ Ψ₁ v ω) ∂ν = - Z' v := by
      simp only [hZ']
      rw [integral_neg, neg_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
    unfold meanDerivAlongSegment
    rw [hmean, hmean, hmean, hmean, a1, a2, a3, a4]
    have hz := (hZpos v).ne'
    field_simp
    ring
  have hends : weightedMean μ w Ψ₁ A₁ - weightedMean μ w Ψ₀ A₀ = N 1 / Z 1 - N 0 / Z 0 := by
    have s1 : segmentPoint Ψ₀ Ψ₁ 1 = Ψ₁ := by funext ω; simp [segmentPoint]
    have s0 : segmentPoint Ψ₀ Ψ₁ 0 = Ψ₀ := by funext ω; simp [segmentPoint]
    have m1 : weightedMean μ w Ψ₁ A₁ = N 1 / Z 1 := by
      have := hmean 1 A₁
      rw [s1] at this
      rw [this]
      congr 1
      simp only [hN, hG₁, hG₀]
      simp only [one_mul, sub_self, zero_mul, add_zero]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
    have m0 : weightedMean μ w Ψ₀ A₀ = N 0 / Z 0 := by
      have := hmean 0 A₀
      rw [s0] at this
      rw [this]
      congr 1
      simp only [hN, hG₁, hG₀]
      simp only [zero_mul, sub_zero, one_mul, zero_add]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
    rw [m1, m0]
  rw [hends]
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v => N v / Z v) (s := Set.Icc (0 : ℝ) 1) (C := B) (x := 0) (y := 1)
    (fun v _ => (dm v).hasDerivWithinAt)
    (fun v hv => by
      have := hB v hv.1 hv.2
      rw [hslope] at this
      rw [Real.norm_eq_abs]
      exact this)
    (convex_Icc 0 1) (by simp) (by simp)
  simpa [Real.norm_eq_abs] using hmv
end YangMills.Construction.DensityMeans
end
