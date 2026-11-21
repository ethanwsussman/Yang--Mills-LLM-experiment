import YangMills.Construction.ColdStepAtMirrorFrames.BirthsAlongTwoSegments
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmAlongASegmentOfWeights
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace GibbsSegment
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
theorem gibbsMean_continuous_segment (A B H : Ω → ℝ) (M K : ℝ) (hA : Measurable A) (hB : Measurable B)
    (hH : Measurable H) (hAM : ∀ ω, |A ω| ≤ M) (hBM : ∀ ω, |B ω| ≤ M) (hHK : ∀ ω, |H ω| ≤ K)
    (hμ : μ ≠ 0) :
    Continuous fun τ : ℝ => gibbsMean μ (fun ω => τ * B ω + (1 - τ) * A ω) H := by
  have : NeZero μ := ⟨hμ⟩
  have hnum : ∀ (G : Ω → ℝ) (Kg : ℝ), Measurable G → (∀ ω, |G ω| ≤ Kg) →
      Continuous fun τ : ℝ => ∫ ω, G ω * Real.exp (-(τ * B ω + (1 - τ) * A ω)) ∂μ := by
    intro G Kg hG hGK
    rw [continuous_iff_continuousAt]
    intro τ₀
    apply continuousAt_of_dominated (bound := fun _ => Kg * Real.exp ((2 * |τ₀| + 4) * M))
    · exact Filter.Eventually.of_forall fun τ => (hG.mul (by fun_prop)).aestronglyMeasurable
    · have hb : Metric.ball τ₀ 1 ∈ nhds τ₀ := Metric.ball_mem_nhds _ one_pos
      filter_upwards [hb] with τ hτ
      refine Filter.Eventually.of_forall fun ω => ?_
      have hτ' : |τ - τ₀| < 1 := by simpa [Real.dist_eq] using hτ
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hK : 0 ≤ Kg := (abs_nonneg _).trans (hGK ω)
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hAM ω)
      apply mul_le_mul (hGK ω) _ (Real.exp_pos _).le hK
      apply Real.exp_le_exp.mpr
      have h1 : |τ| ≤ |τ₀| + 1 := by
        have := abs_sub_abs_le_abs_sub τ τ₀
        linarith
      have h2 : |1 - τ| ≤ |τ₀| + 2 := by
        have := abs_sub 1 τ
        simp only [abs_one] at this
        linarith
      have h3 : |τ * B ω + (1 - τ) * A ω| ≤ (|τ₀| + 1) * M + (|τ₀| + 2) * M := by
        calc |τ * B ω + (1 - τ) * A ω| ≤ |τ * B ω| + |(1 - τ) * A ω| := abs_add_le _ _
          _ = |τ| * |B ω| + |1 - τ| * |A ω| := by rw [abs_mul, abs_mul]
          _ ≤ (|τ₀| + 1) * M + (|τ₀| + 2) * M := by
            gcongr
            · exact hBM ω
            · exact hAM ω
      have := neg_abs_le (τ * B ω + (1 - τ) * A ω)
      nlinarith
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun ω => by
        have : Continuous fun τ : ℝ => G ω * Real.exp (-(τ * B ω + (1 - τ) * A ω)) := by
          fun_prop
        exact this.continuousAt
  have hden : ∀ τ : ℝ, (∫ ω, 1 * Real.exp (-(τ * B ω + (1 - τ) * A ω)) ∂μ) ≠ 0 := by
    intro τ
    simp only [one_mul]
    apply ne_of_gt
    apply integral_exp_pos
    refine Integrable.of_bound ((by fun_prop : Measurable fun ω =>
      Real.exp (-(τ * B ω + (1 - τ) * A ω))).aestronglyMeasurable)
      (Real.exp ((|τ| + |1 - τ|) * M)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h3 : |τ * B ω + (1 - τ) * A ω| ≤ (|τ| + |1 - τ|) * M := by
      calc |τ * B ω + (1 - τ) * A ω| ≤ |τ * B ω| + |(1 - τ) * A ω| := abs_add_le _ _
        _ = |τ| * |B ω| + |1 - τ| * |A ω| := by rw [abs_mul, abs_mul]
        _ ≤ |τ| * M + |1 - τ| * M := by
          gcongr
          · exact hBM ω
          · exact hAM ω
        _ = _ := by ring
    have := neg_abs_le (τ * B ω + (1 - τ) * A ω)
    linarith
  have c1 := hnum H K hH hHK
  have c2 := hnum (fun _ => 1) 1 measurable_const (by simp)
  have := c1.div c2 hden
  refine this.congr fun τ => ?_
  simp only [one_mul, gibbsMean, Pi.div_apply]
theorem gibbsMean_finset_sum_segment {P : Type} [Fintype P] (A B : Ω → ℝ) (H : P → Ω → ℝ) (D : Ω → ℝ) (M K : ℝ)
    (hA : Measurable A) (hB : Measurable B) (hH : ∀ Y, Measurable (H Y))
    (hAM : ∀ ω, |A ω| ≤ M) (hBM : ∀ ω, |B ω| ≤ M) (hHK : ∀ Y ω, |H Y ω| ≤ K)
    (hD : ∀ ω, D ω = ∑ Y, H Y ω) (τ : ℝ) :
    (∫ ω, D ω * Real.exp (-(τ * B ω + (1 - τ) * A ω)) ∂μ) /
        (∫ ω, Real.exp (-(τ * B ω + (1 - τ) * A ω)) ∂μ) =
      ∑ Y, gibbsMean μ (fun ω => τ * B ω + (1 - τ) * A ω) (H Y) := by
  have hint : ∀ Y, Integrable (fun ω => H Y ω * Real.exp (-(τ * B ω + (1 - τ) * A ω))) μ := by
    intro Y
    refine Integrable.of_bound (((hH Y).mul (by fun_prop)).aestronglyMeasurable)
      (K * Real.exp ((|τ| + |1 - τ|) * M)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hK : 0 ≤ K := (abs_nonneg _).trans (hHK Y ω)
    apply mul_le_mul (hHK Y ω) _ (Real.exp_pos _).le hK
    apply Real.exp_le_exp.mpr
    have h3 : |τ * B ω + (1 - τ) * A ω| ≤ (|τ| + |1 - τ|) * M := by
      calc |τ * B ω + (1 - τ) * A ω| ≤ |τ * B ω| + |(1 - τ) * A ω| := abs_add_le _ _
        _ = |τ| * |B ω| + |1 - τ| * |A ω| := by rw [abs_mul, abs_mul]
        _ ≤ |τ| * M + |1 - τ| * M := by
          gcongr
          · exact hBM ω
          · exact hAM ω
        _ = _ := by ring
    have := neg_abs_le (τ * B ω + (1 - τ) * A ω)
    linarith
  have e : ∀ ω, D ω * Real.exp (-(τ * B ω + (1 - τ) * A ω)) =
      ∑ Y, H Y ω * Real.exp (-(τ * B ω + (1 - τ) * A ω)) := by
    intro ω
    rw [hD, Finset.sum_mul]
  simp only [e]
  rw [integral_finset_sum _ fun Y _ => hint Y, Finset.sum_div]
  rfl
end GibbsSegment
open GibbsSegment in
theorem logPartitionTwoSegmentsLocalDecomposition_of_interpolation (hlog : LogPartitionInterpolation) :
    LogPartitionTwoSegmentsLocalDecomposition := by
  intro Ω _ μ _ P _ ψ q G M hμ hψ hq hG hψM hqM hGM
  set Ψ : Ω → ℝ := fun ω => ∑ Y, ψ Y ω with hΨ
  set Q : Ω → ℝ := fun ω => ∑ Y, q Y ω with hQ
  set R : Ω → ℝ := fun ω => ∑ Y, G Y ω with hR
  set N : ℝ := (Fintype.card P : ℝ) * M with hN
  have hsum : ∀ (g : P → Ω → ℝ), (∀ Y ω, |g Y ω| ≤ M) → ∀ ω, |∑ Y, g Y ω| ≤ N := by
    intro g hg ω
    calc |∑ Y, g Y ω| ≤ ∑ Y, |g Y ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _Y : P, M := Finset.sum_le_sum fun Y _ => hg Y ω
      _ = N := by simp [hN]
  have hΨm : Measurable Ψ := Finset.measurable_fun_sum _ fun Y _ => hψ Y
  have hQm : Measurable Q := Finset.measurable_fun_sum _ fun Y _ => hq Y
  have hRm : Measurable R := Finset.measurable_fun_sum _ fun Y _ => hG Y
  have hΨN := hsum ψ hψM
  have hQN := hsum q hqM
  have hRN := hsum G hGM
  have hBN : ∀ ω, |Ψ ω - R ω| ≤ 2 * N := fun ω => by
    have h1 := abs_sub (Ψ ω) (R ω)
    have h2 := hΨN ω
    have h3 := hRN ω
    linarith
  have hΨ2 : ∀ ω, |Ψ ω| ≤ 2 * N := fun ω => by
    have h2 := hΨN ω
    have h3 := abs_nonneg (Ψ ω)
    linarith
  have hQ2 : ∀ ω, |Q ω| ≤ 2 * N := fun ω => by
    have h2 := hQN ω
    have h3 := abs_nonneg (Q ω)
    linarith
  have s1 := hlog Ω μ Q Ψ (2 * N) hμ hQm hΨm hQ2 hΨ2
  have s2 := hlog Ω μ Ψ (fun ω => Ψ ω - R ω) (2 * N) hμ hΨm (hΨm.sub hRm) hΨ2 hBN
  have hd1 : ∀ Y, ∀ ω, |ψ Y ω - q Y ω| ≤ 2 * M := by
    intro Y ω
    have h1 := abs_sub (ψ Y ω) (q Y ω)
    have h2 := hψM Y ω
    have h3 := hqM Y ω
    linarith
  have hseg1 : ∀ τ : ℝ, (∫ ω, (Ψ ω - Q ω) * Real.exp (-(τ * Ψ ω + (1 - τ) * Q ω)) ∂μ) /
      (∫ ω, Real.exp (-(τ * Ψ ω + (1 - τ) * Q ω)) ∂μ) =
      ∑ Y, gibbsMean μ (fun ω => τ * Ψ ω + (1 - τ) * Q ω) (fun ω => ψ Y ω - q Y ω) := fun τ =>
    gibbsMean_finset_sum_segment (μ := μ) Q Ψ (fun Y ω => ψ Y ω - q Y ω) (fun ω => Ψ ω - Q ω) (2 * N) (2 * M) hQm hΨm
      (fun Y => (hψ Y).sub (hq Y)) hQ2 hΨ2 hd1
      (fun ω => by simp only [hΨ, hQ, Finset.sum_sub_distrib]) τ
  have hline : ∀ (ν : ℝ) (ω : Ω), ν * (Ψ ω - R ω) + (1 - ν) * Ψ ω = Ψ ω - ν * R ω := by
    intro ν ω
    ring
  have hseg2 : ∀ ν : ℝ, (∫ ω, ((Ψ ω - R ω) - Ψ ω) * Real.exp (-(ν * (Ψ ω - R ω) + (1 - ν) * Ψ ω)) ∂μ) /
      (∫ ω, Real.exp (-(ν * (Ψ ω - R ω) + (1 - ν) * Ψ ω)) ∂μ) =
      - ∑ Y, gibbsMean μ (fun ω => Ψ ω - ν * R ω) (G Y) := by
    intro ν
    have h := gibbsMean_finset_sum_segment (μ := μ) Ψ (fun ω => Ψ ω - R ω) (fun Y ω => - G Y ω) (fun ω => (Ψ ω - R ω) - Ψ ω)
      (2 * N) M hΨm (hΨm.sub hRm) (fun Y => (hG Y).neg) hΨ2 hBN
      (fun Y ω => by simpa using hGM Y ω)
      (fun ω => by simp only [hR, Finset.sum_neg_distrib]; ring) ν
    rw [h, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro Y _
    simp only [gibbsMean, hline, neg_mul, integral_neg, neg_div]
  have hc1 : ∀ Y, Continuous fun τ : ℝ =>
      gibbsMean μ (fun ω => τ * Ψ ω + (1 - τ) * Q ω) (fun ω => ψ Y ω - q Y ω) := fun Y =>
    gibbsMean_continuous_segment (μ := μ) Q Ψ _ (2 * N) (2 * M) hQm hΨm ((hψ Y).sub (hq Y)) hQ2 hΨ2 (hd1 Y) hμ
  have hc2 : ∀ Y, Continuous fun ν : ℝ =>
      gibbsMean μ (fun ω => Ψ ω - ν * R ω) (G Y) := by
    intro Y
    have h := gibbsMean_continuous_segment (μ := μ) Ψ (fun ω => Ψ ω - R ω) (G Y) (2 * N) M hΨm (hΨm.sub hRm) (hG Y) hΨ2 hBN
      (hGM Y) hμ
    simpa only [hline] using h
  simp only [hseg1] at s1
  simp only [hseg2] at s2
  have i1 : (∫ τ in (0 : ℝ)..1, ∑ Y, gibbsMean μ (fun ω => τ * Ψ ω + (1 - τ) * Q ω)
      (fun ω => ψ Y ω - q Y ω)) = ∑ Y, ∫ τ in (0 : ℝ)..1,
        gibbsMean μ (fun ω => τ * Ψ ω + (1 - τ) * Q ω) (fun ω => ψ Y ω - q Y ω) :=
    intervalIntegral.integral_finset_sum fun Y _ => (hc1 Y).intervalIntegrable _ _
  have i2 : (∫ ν in (0 : ℝ)..1, - ∑ Y, gibbsMean μ (fun ω => Ψ ω - ν * R ω) (G Y)) =
      - ∑ Y, ∫ ν in (0 : ℝ)..1, gibbsMean μ (fun ω => Ψ ω - ν * R ω) (G Y) := by
    rw [intervalIntegral.integral_neg]
    congr 1
    exact intervalIntegral.integral_finset_sum fun Y _ => (hc2 Y).intervalIntegrable _ _
  rw [i1] at s1
  rw [i2] at s2
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
