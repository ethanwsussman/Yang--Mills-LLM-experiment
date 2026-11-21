import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongASegmentProof
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmAlongASegmentOfWeights
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace LogPartition
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {A B : Ω → ℝ} {M : ℝ}
def segmentWeight (A B : Ω → ℝ) (τ : ℝ) (ω : Ω) : ℝ := Real.exp (-(τ * B ω + (1 - τ) * A ω))
theorem measurable_segmentWeight (hA : Measurable A) (hB : Measurable B) (τ : ℝ) :
    Measurable (segmentWeight A B τ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SegmentMean.measurable_segmentExp <;> assumption
theorem abs_segmentWeight_le (hAM : ∀ ω, |A ω| ≤ M) (hBM : ∀ ω, |B ω| ≤ M) (τ₀ τ : ℝ)
    (hτ : |τ - τ₀| < 1) (ω : Ω) :
    |segmentWeight A B τ ω| ≤ Real.exp ((2 * |τ₀| + 4) * M) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SegmentMean.abs_segmentExp_le <;> assumption
theorem hasDerivAt_integral_mul_segmentWeight (H : Ω → ℝ) (K : ℝ) (hH : Measurable H)
    (hHK : ∀ ω, |H ω| ≤ K) (hA : Measurable A) (hB : Measurable B) (hAM : ∀ ω, |A ω| ≤ M)
    (hBM : ∀ ω, |B ω| ≤ M) (τ₀ : ℝ) :
    HasDerivAt (fun τ => ∫ ω, H ω * segmentWeight A B τ ω ∂μ)
      (∫ ω, -(H ω * (B ω - A ω) * segmentWeight A B τ₀ ω) ∂μ) τ₀ := by
  set b : ℝ := K * (2 * M) * Real.exp ((2 * |τ₀| + 4) * M) with hb
  have hint : ∀ τ, |τ - τ₀| < 1 → Integrable (fun ω => H ω * segmentWeight A B τ ω) μ := by
    intro τ hτ
    refine Integrable.of_bound ((hH.mul (measurable_segmentWeight hA hB τ)).aestronglyMeasurable)
      (K * Real.exp ((2 * |τ₀| + 4) * M)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hK : 0 ≤ K := (abs_nonneg _).trans (hHK ω)
    exact mul_le_mul (hHK ω) (abs_segmentWeight_le hAM hBM τ₀ τ hτ ω) (abs_nonneg _) hK
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := τ₀)
    (s := Metric.ball τ₀ 1) (F := fun τ ω => H ω * segmentWeight A B τ ω)
    (F' := fun τ ω => -(H ω * (B ω - A ω) * segmentWeight A B τ ω)) (bound := fun _ => b)
    (Metric.ball_mem_nhds τ₀ one_pos)
    (Filter.Eventually.of_forall fun τ =>
      (hH.mul (measurable_segmentWeight hA hB τ)).aestronglyMeasurable)
    (hint τ₀ (by simp))
    ((((hH.mul (hB.sub hA)).mul (measurable_segmentWeight hA hB τ₀)).neg).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω τ hτ => ?_)
    (integrable_const _)
    (Filter.Eventually.of_forall fun ω τ _ => ?_)
  · exact key.2
  · have hτ' : |τ - τ₀| < 1 := by simpa [Real.dist_eq] using hτ
    rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul]
    have hK : 0 ≤ K := (abs_nonneg _).trans (hHK ω)
    have hM : 0 ≤ M := (abs_nonneg _).trans (hAM ω)
    have hd : |B ω - A ω| ≤ 2 * M := by
      have := abs_sub (B ω) (A ω)
      have h1 := hAM ω
      have h2 := hBM ω
      linarith
    simp only [hb]
    exact mul_le_mul (mul_le_mul (hHK ω) hd (abs_nonneg _) hK)
      (abs_segmentWeight_le hAM hBM τ₀ τ hτ' ω) (abs_nonneg _) (by positivity)
  · unfold segmentWeight
    have h1 : HasDerivAt (fun y : ℝ => -(y * B ω + (1 - y) * A ω)) (-(B ω - A ω)) τ := by
      have e1 : HasDerivAt (fun y : ℝ => y * B ω) (B ω) τ := by
        simpa using (hasDerivAt_id τ).mul_const (B ω)
      have e2 : HasDerivAt (fun y : ℝ => (1 - y) * A ω) (-(A ω)) τ := by
        have h0 : HasDerivAt (fun y : ℝ => 1 - y) (-1) τ := by
          simpa using (hasDerivAt_id τ).const_sub 1
        exact HasDerivAt.congr_deriv (h0.mul_const (A ω)) (by ring)
      exact HasDerivAt.congr_deriv (e1.add e2).neg (by ring)
    have h2 := (h1.exp).const_mul (H ω)
    exact HasDerivAt.congr_deriv h2 (by ring)
end LogPartition
open LogPartition in
theorem logPartitionInterpolation_holds :
    YangMills.Construction.ColdStepAtMirrorFrames.LogPartitionInterpolation := by
  intro Ω _ μ _ A B M hμ hA hB hAM hBM
  haveI : NeZero μ := ⟨hμ⟩
  set Z : ℝ → ℝ := fun τ => ∫ ω, 1 * segmentWeight A B τ ω ∂μ with hZ
  set N : ℝ → ℝ := fun τ => ∫ ω, (B ω - A ω) * segmentWeight A B τ ω ∂μ with hN
  have hone : ∀ ω : Ω, |(1 : ℝ)| ≤ 1 := fun _ => by simp
  have hdiff : ∀ ω, |B ω - A ω| ≤ 2 * M := by
    intro ω
    have := abs_sub (B ω) (A ω)
    have h1 := hAM ω
    have h2 := hBM ω
    linarith
  have hZd : ∀ τ, HasDerivAt Z (-(N τ)) τ := by
    intro τ
    have h := hasDerivAt_integral_mul_segmentWeight (μ := μ) (fun _ => (1 : ℝ)) 1
      measurable_const hone hA hB hAM hBM τ
    refine HasDerivAt.congr_deriv h ?_
    rw [integral_neg]
    simp only [hN, one_mul]
  have hNd : ∀ τ, DifferentiableAt ℝ N τ := fun τ =>
    (hasDerivAt_integral_mul_segmentWeight (μ := μ) (fun ω => B ω - A ω) (2 * M) (hB.sub hA)
      hdiff hA hB hAM hBM τ).differentiableAt
  have hZpos : ∀ τ, 0 < Z τ := by
    intro τ
    simp only [hZ, one_mul]
    unfold segmentWeight
    apply integral_exp_pos
    refine Integrable.of_bound (measurable_segmentWeight hA hB τ).aestronglyMeasurable
      (Real.exp ((2 * |τ| + 4) * M)) (Filter.Eventually.of_forall fun ω => ?_)
    exact abs_segmentWeight_le hAM hBM τ τ (by simp) ω
  have hlog : ∀ τ, HasDerivAt (fun τ => Real.log (Z τ)) (-(N τ) / Z τ) τ := fun τ =>
    (hZd τ).log (hZpos τ).ne'
  have hcont : Continuous fun τ => -(N τ) / Z τ := by
    have c1 : Continuous N := continuous_iff_continuousAt.mpr fun τ => (hNd τ).continuousAt
    have c2 : Continuous Z := continuous_iff_continuousAt.mpr fun τ => (hZd τ).continuousAt
    exact c1.neg.div c2 fun τ => (hZpos τ).ne'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun τ _ => hlog τ) (hcont.intervalIntegrable _ _)
  have e0 : Z 0 = ∫ ω, Real.exp (-(A ω)) ∂μ := by
    simp [hZ, segmentWeight]
  have e1 : Z 1 = ∫ ω, Real.exp (-(B ω)) ∂μ := by
    simp [hZ, segmentWeight]
  rw [← e0, ← e1, ← hftc, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro τ _
  simp only [hN, hZ, segmentWeight, one_mul]
  ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
