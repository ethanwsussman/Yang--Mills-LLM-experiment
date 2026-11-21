import YangMills.Construction.ClusterExpansionOfAStep.MixedDifferenceOfALogarithm
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace MixedDifferences
section LineWeights
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
def lineWeight (P Q : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ := Real.exp (-(P ω + t * Q ω))
theorem lineWeight_measurable {P Q : Ω → ℝ} (hP : Measurable P) (hQ : Measurable Q) (t : ℝ) :
    Measurable (lineWeight P Q t) := by
  unfold lineWeight
  fun_prop
theorem abs_lineWeight_le {P Q : Ω → ℝ} {K : ℝ} (hP : ∀ ω, |P ω| ≤ K) (hQ : ∀ ω, |Q ω| ≤ K) (t₀ t : ℝ)
    (ht : |t - t₀| < 1) (ω : Ω) : |lineWeight P Q t ω| ≤ Real.exp ((|t₀| + 2) * K) := by
  unfold lineWeight
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h1 : |t| ≤ |t₀| + 1 := by
    have := abs_sub_abs_le_abs_sub t t₀
    linarith
  have h3 : |P ω + t * Q ω| ≤ K + (|t₀| + 1) * K := by
    calc |P ω + t * Q ω| ≤ |P ω| + |t * Q ω| := abs_add_le _ _
      _ = |P ω| + |t| * |Q ω| := by rw [abs_mul]
      _ ≤ K + (|t₀| + 1) * K := by
        gcongr
        · exact hP ω
        · exact hQ ω
  have := neg_abs_le (P ω + t * Q ω)
  nlinarith
theorem hasDerivAt_integral_affine_mul_lineWeight {P Q H₀ H₁ : Ω → ℝ} {K : ℝ} (hP : Measurable P)
    (hQ : Measurable Q) (h₀ : Measurable H₀) (h₁ : Measurable H₁) (hPK : ∀ ω, |P ω| ≤ K)
    (hQK : ∀ ω, |Q ω| ≤ K) (h₀K : ∀ ω, |H₀ ω| ≤ K) (h₁K : ∀ ω, |H₁ ω| ≤ K) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ ω, (H₀ ω + t * H₁ ω) * lineWeight P Q t ω ∂μ)
      (∫ ω, (H₁ ω - (H₀ ω + t₀ * H₁ ω) * Q ω) * lineWeight P Q t₀ ω ∂μ) t₀ := by
  set T : ℝ := |t₀| + 1 with hT
  set b : ℝ := (K + (K + T * K) * K) * Real.exp ((|t₀| + 2) * K) with hb
  have hline : ∀ t : ℝ, Measurable fun ω => H₀ ω + t * H₁ ω := fun t => h₀.add (h₁.const_mul t)
  have hsize : ∀ t : ℝ, |t - t₀| < 1 → ∀ ω, |H₀ ω + t * H₁ ω| ≤ K + T * K := by
    intro t ht ω
    have h1 : |t| ≤ T := by
      have := abs_sub_abs_le_abs_sub t t₀
      simp only [hT]
      linarith
    calc |H₀ ω + t * H₁ ω| ≤ |H₀ ω| + |t * H₁ ω| := abs_add_le _ _
      _ = |H₀ ω| + |t| * |H₁ ω| := by rw [abs_mul]
      _ ≤ K + T * K := by
        gcongr
        · exact h₀K ω
        · exact h₁K ω
  have hint0 : Integrable (fun ω => (H₀ ω + t₀ * H₁ ω) * lineWeight P Q t₀ ω) μ := by
    refine Integrable.of_bound (((hline t₀).mul (lineWeight_measurable hP hQ t₀)).aestronglyMeasurable)
      ((K + T * K) * Real.exp ((|t₀| + 2) * K)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hK : 0 ≤ K := (abs_nonneg _).trans (h₀K ω)
    have hTn : 0 ≤ T := by positivity
    exact mul_le_mul (hsize t₀ (by simp) ω) (abs_lineWeight_le hPK hQK t₀ t₀ (by simp) ω) (abs_nonneg _)
      (by positivity)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := t₀)
    (s := Metric.ball t₀ 1) (F := fun t ω => (H₀ ω + t * H₁ ω) * lineWeight P Q t ω)
    (F' := fun t ω => (H₁ ω - (H₀ ω + t * H₁ ω) * Q ω) * lineWeight P Q t ω) (bound := fun _ => b)
    (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t =>
      ((hline t).mul (lineWeight_measurable hP hQ t)).aestronglyMeasurable)
    hint0
    (((h₁.sub ((hline t₀).mul hQ)).mul (lineWeight_measurable hP hQ t₀)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω t ht => ?_)
    (integrable_const _)
    (Filter.Eventually.of_forall fun ω t _ => ?_)
  · exact key.2
  · have ht' : |t - t₀| < 1 := by simpa [Real.dist_eq] using ht
    rw [Real.norm_eq_abs, abs_mul]
    have hK : 0 ≤ K := (abs_nonneg _).trans (h₀K ω)
    have hTn : 0 ≤ T := by positivity
    have hd : |H₁ ω - (H₀ ω + t * H₁ ω) * Q ω| ≤ K + (K + T * K) * K := by
      calc |H₁ ω - (H₀ ω + t * H₁ ω) * Q ω| ≤ |H₁ ω| + |(H₀ ω + t * H₁ ω) * Q ω| := abs_sub _ _
        _ = |H₁ ω| + |H₀ ω + t * H₁ ω| * |Q ω| := by rw [abs_mul]
        _ ≤ K + (K + T * K) * K := by
          gcongr
          · exact h₁K ω
          · exact hsize t ht' ω
          · exact hQK ω
    simp only [hb]
    exact mul_le_mul hd (abs_lineWeight_le hPK hQK t₀ t ht' ω) (abs_nonneg _) (by positivity)
  · unfold lineWeight
    have e0 : HasDerivAt (fun y : ℝ => H₀ ω + y * H₁ ω) (H₁ ω) t := by
      simpa using ((hasDerivAt_id t).mul_const (H₁ ω)).const_add (H₀ ω)
    have e1 : HasDerivAt (fun y : ℝ => -(P ω + y * Q ω)) (-(Q ω)) t := by
      have : HasDerivAt (fun y : ℝ => P ω + y * Q ω) (Q ω) t := by
        simpa using ((hasDerivAt_id t).mul_const (Q ω)).const_add (P ω)
      exact this.neg
    have e2 := e0.mul e1.exp
    exact HasDerivAt.congr_deriv e2 (by ring)
end LineWeights
theorem logIntegralMixedDifferenceBound_holds : LogIntegralMixedDifferenceBound := by
  intro Ω _ μ _ U A B C M ε hμ hU hA hB hC hUM hAM hBM hCM hcov
  have : NeZero μ := ⟨hμ⟩
  have hM : 0 ≤ M := by
    by_contra h
    have hne : Nonempty Ω := by
      by_contra hno
      apply hμ
      have : IsEmpty Ω := not_nonempty_iff.mp hno
      exact Measure.eq_zero_of_isEmpty μ
    obtain ⟨ω⟩ := hne
    exact h ((abs_nonneg _).trans (hUM ω))
  set K : ℝ := 2 * M + 1 with hK
  have hK1 : 1 ≤ K := by simp only [hK]; linarith
  have hMK : M ≤ K := by simp only [hK]; linarith
  have hline : ∀ (X Y : Ω → ℝ) (c : ℝ), 0 ≤ c → c ≤ 1 → (∀ ω, |X ω| ≤ M) → (∀ ω, |Y ω| ≤ M) →
      ∀ ω, |X ω + c * Y ω| ≤ K := by
    intro X Y c h0 h1 hX hY ω
    calc |X ω + c * Y ω| ≤ |X ω| + |c * Y ω| := abs_add_le _ _
      _ = |X ω| + |c| * |Y ω| := by rw [abs_mul]
      _ ≤ M + 1 * M := by
        gcongr
        · exact hX ω
        · rw [abs_of_nonneg h0]; exact h1
        · exact hY ω
      _ ≤ K := by simp only [hK]; linarith
  have hone : ∀ ω : Ω, |(1 : ℝ)| ≤ K := fun _ => by simpa using hK1
  have hzero : ∀ ω : Ω, |(0 : ℝ)| ≤ K := fun _ => by simpa using (by linarith : (0 : ℝ) ≤ K)
  have hAK : ∀ ω, |A ω| ≤ K := fun ω => (hAM ω).trans hMK
  have hCK : ∀ ω, |C ω| ≤ K := fun ω => (hCM ω).trans hMK
  have hvside : ∀ v w ω, bilinearExponent U A B C v w ω =
      (U ω + w * B ω) + v * (A ω + w * C ω) := by
    intro v w ω; simp only [bilinearExponent]; ring
  have hwside : ∀ v w ω, bilinearExponent U A B C v w ω =
      (U ω + v * A ω) + w * (B ω + v * C ω) := by
    intro v w ω; simp only [bilinearExponent]; ring
  set Z : ℝ → ℝ → ℝ := fun v w => ∫ ω, Real.exp (-(bilinearExponent U A B C v w ω)) ∂μ with hZ
  set m : ℝ → ℝ → ℝ := fun v w =>
    gibbsMean μ (bilinearExponent U A B C v w) (fun ω => A ω + w * C ω) with hm
  have hsq_meas : ∀ v w, Measurable (bilinearExponent U A B C v w) := by
    intro v w
    unfold bilinearExponent
    fun_prop
  have hsq_size : ∀ v w : ℝ, 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → ∀ ω,
      |bilinearExponent U A B C v w ω| ≤ 4 * M := by
    intro v w h0 h1 h2 h3 ω
    simp only [bilinearExponent]
    have a1 : |v * A ω| ≤ M := by
      rw [abs_mul, abs_of_nonneg h0]
      have := hAM ω
      nlinarith [abs_nonneg (A ω)]
    have a2 : |w * B ω| ≤ M := by
      rw [abs_mul, abs_of_nonneg h2]
      have := hBM ω
      nlinarith [abs_nonneg (B ω)]
    have a3 : |v * w * C ω| ≤ M := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg h0 h2)]
      have h5 := hCM ω
      have h6 : v * w ≤ 1 := by nlinarith
      nlinarith [abs_nonneg (C ω)]
    have a0 := hUM ω
    calc |U ω + v * A ω + w * B ω + v * w * C ω|
        ≤ |U ω + v * A ω + w * B ω| + |v * w * C ω| := abs_add_le _ _
      _ ≤ |U ω + v * A ω| + |w * B ω| + |v * w * C ω| := by gcongr; exact abs_add_le _ _
      _ ≤ |U ω| + |v * A ω| + |w * B ω| + |v * w * C ω| := by gcongr; exact abs_add_le _ _
      _ ≤ 4 * M := by linarith
  have hint_exp : ∀ v w : ℝ, 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → ∀ (H : Ω → ℝ) (G : ℝ), Measurable H →
      (∀ ω, |H ω| ≤ G) → Integrable (fun ω => H ω * Real.exp (-(bilinearExponent U A B C v w ω))) μ := by
    intro v w h0 h1 h2 h3 H G hH hHK
    refine Integrable.of_bound
      ((hH.mul ((hsq_meas v w).neg.exp)).aestronglyMeasurable)
      (G * Real.exp (4 * M)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hs := hsq_size v w h0 h1 h2 h3 ω
    have h5 : Real.exp (-(bilinearExponent U A B C v w ω)) ≤ Real.exp (4 * M) := by
      apply Real.exp_le_exp.mpr
      have := neg_abs_le (bilinearExponent U A B C v w ω)
      linarith
    exact mul_le_mul (hHK ω) h5 (Real.exp_pos _).le ((abs_nonneg _).trans (hHK ω))
  have hZpos : ∀ v w : ℝ, 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 → 0 < Z v w := by
    intro v w h0 h1 h2 h3
    have hi := hint_exp v w h0 h1 h2 h3 (fun _ => 1) 1 measurable_const (fun ω => by simp)
    simp only [one_mul] at hi
    exact integral_exp_pos hi
  have hdv : ∀ v w : ℝ, 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
      HasDerivAt (fun v' => Real.log (Z v' w)) (-(m v w)) v := by
    intro v w h0 h1 h2 h3
    have hP : Measurable fun ω => U ω + w * B ω := hU.add (hB.const_mul w)
    have hQ : Measurable fun ω => A ω + w * C ω := hA.add (hC.const_mul w)
    have hd := hasDerivAt_integral_affine_mul_lineWeight (μ := μ) (P := fun ω => U ω + w * B ω)
      (Q := fun ω => A ω + w * C ω)
      (H₀ := fun _ => 1) (H₁ := fun _ => 0) (K := K) hP hQ measurable_const measurable_const
      (hline U B w h2 h3 hUM hBM) (hline A C w h2 h3 hAM hCM) hone hzero v
    have hZeq : (fun t => ∫ ω, ((1 : ℝ) + t * 0) * lineWeight (fun ω => U ω + w * B ω)
        (fun ω => A ω + w * C ω) t ω ∂μ) = fun v' => Z v' w := by
      funext t
      simp only [hZ]
      congr 1
      funext ω
      simp only [lineWeight, mul_zero, add_zero, one_mul, hvside]
    rw [hZeq] at hd
    have hlog := hd.log (hZpos v w h0 h1 h2 h3).ne'
    refine HasDerivAt.congr_deriv hlog ?_
    have hI : (∫ ω, ((0 : ℝ) - (1 + v * 0) * (A ω + w * C ω)) * lineWeight (fun ω => U ω + w * B ω)
        (fun ω => A ω + w * C ω) v ω ∂μ) =
        -∫ ω, (A ω + w * C ω) * Real.exp (-(bilinearExponent U A B C v w ω)) ∂μ := by
      rw [← integral_neg]
      congr 1
      funext ω
      simp only [lineWeight, hvside]
      ring
    rw [hI]
    simp only [hm, gibbsMean, hZ]
    rw [neg_div]
  have hdw : ∀ v w : ℝ, 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
      HasDerivAt (fun w' => m v w')
        (gibbsMean μ (bilinearExponent U A B C v w) C -
          gibbsMean μ (bilinearExponent U A B C v w) (fun ω => (A ω + w * C ω) * (B ω + v * C ω)) +
          gibbsMean μ (bilinearExponent U A B C v w) (fun ω => A ω + w * C ω) *
            gibbsMean μ (bilinearExponent U A B C v w) (fun ω => B ω + v * C ω)) w := by
    intro v w h0 h1 h2 h3
    have hP : Measurable fun ω => U ω + v * A ω := hU.add (hA.const_mul v)
    have hQ : Measurable fun ω => B ω + v * C ω := hB.add (hC.const_mul v)
    have hPK := hline U A v h0 h1 hUM hAM
    have hQK := hline B C v h0 h1 hBM hCM
    have hN := hasDerivAt_integral_affine_mul_lineWeight (μ := μ) (P := fun ω => U ω + v * A ω)
      (Q := fun ω => B ω + v * C ω)
      (H₀ := A) (H₁ := C) (K := K) hP hQ hA hC hPK hQK hAK hCK w
    have hD := hasDerivAt_integral_affine_mul_lineWeight (μ := μ) (P := fun ω => U ω + v * A ω)
      (Q := fun ω => B ω + v * C ω)
      (H₀ := fun _ => 1) (H₁ := fun _ => 0) (K := K) hP hQ measurable_const measurable_const
      hPK hQK hone hzero w
    have hew : ∀ t ω, lineWeight (fun ω => U ω + v * A ω) (fun ω => B ω + v * C ω) t ω =
        Real.exp (-(bilinearExponent U A B C v t ω)) := by
      intro t ω
      simp only [lineWeight, hwside]
    have hDeq : (fun t => ∫ ω, ((1 : ℝ) + t * 0) * lineWeight (fun ω => U ω + v * A ω)
        (fun ω => B ω + v * C ω) t ω ∂μ) = fun t => Z v t := by
      funext t
      simp only [hZ]
      congr 1
      funext ω
      simp only [hew, mul_zero, add_zero, one_mul]
    rw [hDeq] at hD
    have hZ0 := hZpos v w h0 h1 h2 h3
    have hq := hN.div hD hZ0.ne'
    have hfun : ((fun t => ∫ ω, (A ω + t * C ω) * lineWeight (fun ω => U ω + v * A ω)
        (fun ω => B ω + v * C ω) t ω ∂μ) / fun t => Z v t) = fun w' => m v w' := by
      funext t
      simp only [Pi.div_apply, hm, gibbsMean, hZ, hew]
    rw [hfun] at hq
    refine HasDerivAt.congr_deriv hq ?_
    set e : Ω → ℝ := fun ω => Real.exp (-(bilinearExponent U A B C v w ω)) with he
    have iC := hint_exp v w h0 h1 h2 h3 C K hC hCK
    have iX := hint_exp v w h0 h1 h2 h3 (fun ω => (A ω + w * C ω) * (B ω + v * C ω)) (K * K)
      ((hA.add (hC.const_mul w)).mul hQ) (fun ω => by
        rw [abs_mul]
        exact mul_le_mul (hline A C w h2 h3 hAM hCM ω) (hQK ω) (abs_nonneg _) (by linarith))
    have e1 : (∫ ω, (C ω - (A ω + w * C ω) * (B ω + v * C ω)) * lineWeight (fun ω => U ω + v * A ω)
        (fun ω => B ω + v * C ω) w ω ∂μ) =
        (∫ ω, C ω * e ω ∂μ) - ∫ ω, (A ω + w * C ω) * (B ω + v * C ω) * e ω ∂μ := by
      rw [← integral_sub iC iX]
      congr 1
      funext ω
      simp only [hew, he]
      ring
    have e2 : (∫ ω, ((0 : ℝ) - (1 + w * 0) * (B ω + v * C ω)) * lineWeight (fun ω => U ω + v * A ω)
        (fun ω => B ω + v * C ω) w ω ∂μ) = -∫ ω, (B ω + v * C ω) * e ω ∂μ := by
      rw [← integral_neg]
      congr 1
      funext ω
      simp only [hew, he]
      ring
    have e3 : (∫ ω, (A ω + w * C ω) * lineWeight (fun ω => U ω + v * A ω)
        (fun ω => B ω + v * C ω) w ω ∂μ) = ∫ ω, (A ω + w * C ω) * e ω ∂μ := by
      congr 1
      funext ω
      simp only [hew, he]
    have w1 : gibbsMean μ (bilinearExponent U A B C v w) C = (∫ ω, C ω * e ω ∂μ) / Z v w := rfl
    have w2 : gibbsMean μ (bilinearExponent U A B C v w)
        (fun ω => (A ω + w * C ω) * (B ω + v * C ω)) =
        (∫ ω, (A ω + w * C ω) * (B ω + v * C ω) * e ω ∂μ) / Z v w := rfl
    have w3 : gibbsMean μ (bilinearExponent U A B C v w) (fun ω => A ω + w * C ω) =
        (∫ ω, (A ω + w * C ω) * e ω ∂μ) / Z v w := rfl
    have w4 : gibbsMean μ (bilinearExponent U A B C v w) (fun ω => B ω + v * C ω) =
        (∫ ω, (B ω + v * C ω) * e ω ∂μ) / Z v w := rfl
    rw [e1, e2, e3, w1, w2, w3, w4]
    generalize (∫ ω, C ω * e ω ∂μ) = a1
    generalize (∫ ω, (A ω + w * C ω) * (B ω + v * C ω) * e ω ∂μ) = a2
    generalize (∫ ω, (A ω + w * C ω) * e ω ∂μ) = a3
    generalize (∫ ω, (B ω + v * C ω) * e ω ∂μ) = a4
    have hz : Z v w ≠ 0 := hZ0.ne'
    generalize Z v w = z at hz ⊢
    field_simp
    ring
  have hmw : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ‖m v 1 - m v 0‖ ≤ ε := by
    intro v h0 h1
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun w' => m v w')
      (f' := fun w => gibbsMean μ (bilinearExponent U A B C v w) C -
          gibbsMean μ (bilinearExponent U A B C v w) (fun ω => (A ω + w * C ω) * (B ω + v * C ω)) +
          gibbsMean μ (bilinearExponent U A B C v w) (fun ω => A ω + w * C ω) *
            gibbsMean μ (bilinearExponent U A B C v w) (fun ω => B ω + v * C ω))
      (s := Set.Icc (0 : ℝ) 1) (C := ε) (x := 0) (y := 1)
      (fun w hw => (hdw v w h0 h1 hw.1 hw.2).hasDerivWithinAt)
      (fun w hw => by
        have := hcov v w h0 h1 hw.1 hw.2
        rw [Real.norm_eq_abs]
        rw [← abs_neg]
        convert this using 2
        ring)
      (convex_Icc _ _) (by simp) (by simp)
    simpa using this
  have hfin := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun v' => Real.log (Z v' 1) - Real.log (Z v' 0))
      (f' := fun v => -(m v 1) - -(m v 0))
      (s := Set.Icc (0 : ℝ) 1) (C := ε) (x := 0) (y := 1)
      (fun v hv => ((hdv v 1 hv.1 hv.2 (by simp) (by simp)).sub
        (hdv v 0 hv.1 hv.2 (by simp) (by simp))).hasDerivWithinAt)
      (fun v hv => by
        have := hmw v hv.1 hv.2
        rw [Real.norm_eq_abs] at this ⊢
        rw [← abs_neg]
        convert this using 2
        ring)
      (convex_Icc _ _) (by simp) (by simp)
  simp only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hfin
  have hgoal : Real.log (Z 1 1) + Real.log (Z 0 0) - Real.log (Z 1 0) - Real.log (Z 0 1) =
      Real.log (Z 1 1) - Real.log (Z 1 0) - (Real.log (Z 0 1) - Real.log (Z 0 0)) := by ring
  show |Real.log (Z 1 1) + Real.log (Z 0 0) - Real.log (Z 1 0) - Real.log (Z 0 1)| ≤ ε
  rw [hgoal]
  exact hfin
end MixedDifferences
end YangMills.Construction
end
