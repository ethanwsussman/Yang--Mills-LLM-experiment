import YangMills.Construction.ClusterExpansionOfAStep.SecondMomentOfAConvexLawProof
import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace SegmentMean
section Finite
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {A B : Ω → ℝ} {M : ℝ}
def segmentExp (A B : Ω → ℝ) (τ : ℝ) (ω : Ω) : ℝ := Real.exp (-(τ * B ω + (1 - τ) * A ω))
theorem measurable_segmentExp (hA : Measurable A) (hB : Measurable B) (τ : ℝ) :
    Measurable (segmentExp A B τ) := by
  unfold segmentExp
  fun_prop
theorem abs_segmentExp_le (hAM : ∀ ω, |A ω| ≤ M) (hBM : ∀ ω, |B ω| ≤ M) (τ₀ τ : ℝ) (hτ : |τ - τ₀| < 1)
    (ω : Ω) : |segmentExp A B τ ω| ≤ Real.exp ((2 * |τ₀| + 4) * M) := by
  unfold segmentExp
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hM : 0 ≤ M := (abs_nonneg _).trans (hAM ω)
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
theorem integrable_mul_segmentExp (H : Ω → ℝ) (K : ℝ) (hH : Measurable H) (hHK : ∀ ω, |H ω| ≤ K)
    (hA : Measurable A) (hB : Measurable B) (hAM : ∀ ω, |A ω| ≤ M) (hBM : ∀ ω, |B ω| ≤ M) (τ : ℝ) :
    Integrable (fun ω => H ω * segmentExp A B τ ω) μ := by
  refine Integrable.of_bound ((hH.mul (measurable_segmentExp hA hB τ)).aestronglyMeasurable)
    (K * Real.exp ((2 * |τ| + 4) * M)) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hK : 0 ≤ K := (abs_nonneg _).trans (hHK ω)
  exact mul_le_mul (hHK ω) (abs_segmentExp_le hAM hBM τ τ (by simp) ω) (abs_nonneg _) hK
theorem hasDerivAt_integral_mul_segmentExp (H : Ω → ℝ) (K : ℝ) (hH : Measurable H)
    (hHK : ∀ ω, |H ω| ≤ K) (hA : Measurable A) (hB : Measurable B) (hAM : ∀ ω, |A ω| ≤ M)
    (hBM : ∀ ω, |B ω| ≤ M) (τ₀ : ℝ) :
    HasDerivAt (fun τ => ∫ ω, H ω * segmentExp A B τ ω ∂μ)
      (-∫ ω, (H ω * (B ω - A ω)) * segmentExp A B τ₀ ω ∂μ) τ₀ := by
  set b : ℝ := K * (2 * M) * Real.exp ((2 * |τ₀| + 4) * M) with hb
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := τ₀)
    (s := Metric.ball τ₀ 1) (F := fun τ ω => H ω * segmentExp A B τ ω)
    (F' := fun τ ω => -(H ω * (B ω - A ω) * segmentExp A B τ ω)) (bound := fun _ => b)
    (Metric.ball_mem_nhds τ₀ one_pos)
    (Filter.Eventually.of_forall fun τ =>
      (hH.mul (measurable_segmentExp hA hB τ)).aestronglyMeasurable)
    (integrable_mul_segmentExp H K hH hHK hA hB hAM hBM τ₀)
    ((((hH.mul (hB.sub hA)).mul (measurable_segmentExp hA hB τ₀)).neg).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω τ hτ => ?_)
    (integrable_const _)
    (Filter.Eventually.of_forall fun ω τ _ => ?_)
  · have := key.2
    rw [integral_neg] at this
    exact this
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
    exact mul_le_mul (mul_le_mul (hHK ω) hd (abs_nonneg _) hK) (abs_segmentExp_le hAM hBM τ₀ τ hτ' ω)
      (abs_nonneg _) (by positivity)
  · unfold segmentExp
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
def weightedIntegral (μ : Measure Ω) (A B R : Ω → ℝ) (G : Ω → ℝ) (τ : ℝ) : ℝ :=
  ∫ ω, (R ω * G ω) * segmentExp A B τ ω ∂μ
theorem hasDerivAt_weightedIntegral {R G : Ω → ℝ} {KR KG : ℝ} (hR : Measurable R)
    (hRK : ∀ ω, |R ω| ≤ KR) (hG : Measurable G) (hGK : ∀ ω, |G ω| ≤ KG) (hA : Measurable A)
    (hB : Measurable B) (hAM : ∀ ω, |A ω| ≤ M) (hBM : ∀ ω, |B ω| ≤ M) (τ : ℝ) :
    HasDerivAt (weightedIntegral μ A B R G)
      (-weightedIntegral μ A B R (fun ω => G ω * (B ω - A ω)) τ) τ := by
  have h := hasDerivAt_integral_mul_segmentExp (μ := μ) (fun ω => R ω * G ω) (KR * KG) (hR.mul hG)
    (fun ω => by
      rw [abs_mul]
      have hK : 0 ≤ KR := (abs_nonneg _).trans (hRK ω)
      exact mul_le_mul (hRK ω) (hGK ω) (abs_nonneg _) hK) hA hB hAM hBM τ
  refine HasDerivAt.congr_deriv h ?_
  unfold weightedIntegral
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by ring
theorem weightedIntegral_add_smul {R G G' : Ω → ℝ} {KR KG : ℝ} (hR : Measurable R)
    (hRK : ∀ ω, |R ω| ≤ KR) (hG : Measurable G) (hGK : ∀ ω, |G ω| ≤ KG) (hG' : Measurable G')
    (hGK' : ∀ ω, |G' ω| ≤ KG) (hA : Measurable A) (hB : Measurable B)
    (hAM : ∀ ω, |A ω| ≤ M) (hBM : ∀ ω, |B ω| ≤ M) (s τ : ℝ) :
    weightedIntegral μ A B R (fun ω => G ω + s * G' ω) τ =
      weightedIntegral μ A B R G τ + s * weightedIntegral μ A B R G' τ := by
  have hKR : ∀ ω, |R ω * G ω| ≤ KR * KG := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hRK ω) (hGK ω) (abs_nonneg _) ((abs_nonneg _).trans (hRK ω))
  have hKR' : ∀ ω, |R ω * G' ω| ≤ KR * KG := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hRK ω) (hGK' ω) (abs_nonneg _) ((abs_nonneg _).trans (hRK ω))
  have i1 := integrable_mul_segmentExp (μ := μ) (fun ω => R ω * G ω) (KR * KG) (hR.mul hG) hKR
    hA hB hAM hBM τ
  have i2 := integrable_mul_segmentExp (μ := μ) (fun ω => R ω * G' ω) (KR * KG) (hR.mul hG') hKR'
    hA hB hAM hBM τ
  unfold weightedIntegral
  rw [← integral_const_mul, ← integral_add i1 (i2.const_mul s)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by ring
theorem weightedIntegral_lineMap {R G₀ G₁ : Ω → ℝ} {KR KG : ℝ} (hR : Measurable R)
    (hRK : ∀ ω, |R ω| ≤ KR) (hG₀ : Measurable G₀) (hGK₀ : ∀ ω, |G₀ ω| ≤ KG) (hG₁ : Measurable G₁)
    (hGK₁ : ∀ ω, |G₁ ω| ≤ KG) (hA : Measurable A) (hB : Measurable B) (hAM : ∀ ω, |A ω| ≤ M)
    (hBM : ∀ ω, |B ω| ≤ M) (s τ : ℝ) (hK : 0 ≤ KG) :
    weightedIntegral μ A B R (fun ω => s * G₁ ω + (1 - s) * G₀ ω) τ =
      weightedIntegral μ A B R G₀ τ + s * weightedIntegral μ A B R (fun ω => G₁ ω - G₀ ω) τ := by
  have hdiffK : ∀ ω, |G₁ ω - G₀ ω| ≤ 2 * KG := fun ω => by
    have := abs_sub (G₁ ω) (G₀ ω)
    have h1 := hGK₀ ω
    have h2 := hGK₁ ω
    linarith
  have := weightedIntegral_add_smul (μ := μ) (G := G₀) (G' := fun ω => G₁ ω - G₀ ω) (KG := 2 * KG)
    hR hRK hG₀ (fun ω => (hGK₀ ω).trans (by linarith)) (hG₁.sub hG₀) hdiffK hA hB hAM hBM s τ
  rw [← this]
  congr 1
  funext ω
  ring
theorem hasDerivAt_weightedMean {R G₀ G₁ : Ω → ℝ} {KR KG : ℝ} (hR : Measurable R)
    (hRK : ∀ ω, |R ω| ≤ KR) (hG₀ : Measurable G₀) (hGK₀ : ∀ ω, |G₀ ω| ≤ KG) (hG₁ : Measurable G₁)
    (hGK₁ : ∀ ω, |G₁ ω| ≤ KG) (hA : Measurable A) (hB : Measurable B)
    (hAM : ∀ ω, |A ω| ≤ M) (hBM : ∀ ω, |B ω| ≤ M) (hK : 0 ≤ KG) (hM : 0 ≤ M)
    (hZ : ∀ τ, 0 < weightedIntegral μ A B R (fun _ => 1) τ) (τ : ℝ) :
    HasDerivAt (fun τ => (weightedIntegral μ A B R G₀ τ +
        τ * weightedIntegral μ A B R (fun ω => G₁ ω - G₀ ω) τ) /
        weightedIntegral μ A B R (fun _ => 1) τ)
      (weightedIntegral μ A B R (fun ω => G₁ ω - G₀ ω) τ / weightedIntegral μ A B R (fun _ => 1) τ -
        (weightedIntegral μ A B R (fun ω => (τ * G₁ ω + (1 - τ) * G₀ ω) * (B ω - A ω)) τ /
            weightedIntegral μ A B R (fun _ => 1) τ -
          (weightedIntegral μ A B R (fun ω => τ * G₁ ω + (1 - τ) * G₀ ω) τ /
              weightedIntegral μ A B R (fun _ => 1) τ) *
            (weightedIntegral μ A B R (fun ω => B ω - A ω) τ /
              weightedIntegral μ A B R (fun _ => 1) τ))) τ := by
  have hone : ∀ ω : Ω, |(1 : ℝ)| ≤ 1 := fun _ => by simp
  have hdiffK : ∀ ω, |G₁ ω - G₀ ω| ≤ 2 * KG := fun ω => by
    have := abs_sub (G₁ ω) (G₀ ω)
    have h1 := hGK₀ ω
    have h2 := hGK₁ ω
    linarith
  have hsub : Measurable fun ω => G₁ ω - G₀ ω := hG₁.sub hG₀
  have d0 := hasDerivAt_weightedIntegral (μ := μ) hR hRK hG₀ hGK₀ hA hB hAM hBM τ
  have d1 := hasDerivAt_weightedIntegral (μ := μ) (G := fun ω => G₁ ω - G₀ ω) hR hRK hsub hdiffK
    hA hB hAM hBM τ
  have dz := hasDerivAt_weightedIntegral (μ := μ) (G := fun _ => (1 : ℝ)) hR hRK measurable_const
    hone hA hB hAM hBM τ
  have hnum : HasDerivAt (fun τ => weightedIntegral μ A B R G₀ τ +
      τ * weightedIntegral μ A B R (fun ω => G₁ ω - G₀ ω) τ) _ τ :=
    d0.add ((hasDerivAt_id' τ).mul d1)
  have hq := hnum.div dz (hZ τ).ne'
  refine HasDerivAt.congr_deriv hq ?_
  have hZ0 := (hZ τ).ne'
  have hBA : Measurable fun ω => B ω - A ω := hB.sub hA
  have hBAK : ∀ ω, |B ω - A ω| ≤ 2 * M := fun ω => by
    have := abs_sub (B ω) (A ω)
    have h1 := hAM ω
    have h2 := hBM ω
    linarith
  have e1 := weightedIntegral_lineMap (μ := μ) hR hRK hG₀ hGK₀ hG₁ hGK₁ hA hB hAM hBM τ τ hK
  have e2 : weightedIntegral μ A B R (fun ω => (τ * G₁ ω + (1 - τ) * G₀ ω) * (B ω - A ω)) τ =
      weightedIntegral μ A B R (fun ω => G₀ ω * (B ω - A ω)) τ +
        τ * weightedIntegral μ A B R (fun ω => (G₁ ω - G₀ ω) * (B ω - A ω)) τ := by
    have hK1 : ∀ ω, |G₀ ω * (B ω - A ω)| ≤ (2 * KG) * (2 * M) := fun ω => by
      rw [abs_mul]
      exact mul_le_mul ((hGK₀ ω).trans (by linarith)) (hBAK ω) (abs_nonneg _) (by linarith)
    have hK2 : ∀ ω, |(G₁ ω - G₀ ω) * (B ω - A ω)| ≤ (2 * KG) * (2 * M) := fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hdiffK ω) (hBAK ω) (abs_nonneg _) (by linarith)
    have := weightedIntegral_add_smul (μ := μ) (G := fun ω => G₀ ω * (B ω - A ω))
      (G' := fun ω => (G₁ ω - G₀ ω) * (B ω - A ω)) (KG := (2 * KG) * (2 * M)) hR hRK
      (hG₀.mul hBA) hK1 (hsub.mul hBA) hK2 hA hB hAM hBM τ τ
    rw [← this]
    congr 1
    funext ω
    ring
  rw [e1, e2]
  have e3 : (fun ω => (1 : ℝ) * (B ω - A ω)) = fun ω => B ω - A ω := by
    funext ω
    ring
  rw [e3]
  generalize weightedIntegral μ A B R (fun _ => 1) τ = Z at *
  generalize weightedIntegral μ A B R (fun ω => B ω - A ω) τ = DB at *
  generalize weightedIntegral μ A B R G₀ τ = D0 at *
  generalize weightedIntegral μ A B R (fun ω => G₁ ω - G₀ ω) τ = D1 at *
  generalize weightedIntegral μ A B R (fun ω => G₀ ω * (B ω - A ω)) τ = D2 at *
  generalize weightedIntegral μ A B R (fun ω => (G₁ ω - G₀ ω) * (B ω - A ω)) τ = D3 at *
  field_simp
  ring
theorem abs_weightedMean_sub_le {R G₀ G₁ : Ω → ℝ} {KR KG c : ℝ} (hR : Measurable R)
    (hRK : ∀ ω, |R ω| ≤ KR) (hG₀ : Measurable G₀) (hGK₀ : ∀ ω, |G₀ ω| ≤ KG) (hG₁ : Measurable G₁)
    (hGK₁ : ∀ ω, |G₁ ω| ≤ KG) (hA : Measurable A) (hB : Measurable B)
    (hAM : ∀ ω, |A ω| ≤ M) (hBM : ∀ ω, |B ω| ≤ M) (hK : 0 ≤ KG) (hM : 0 ≤ M)
    (hZ : ∀ τ, 0 < weightedIntegral μ A B R (fun _ => 1) τ)
    (hc : ∀ τ, 0 ≤ τ → τ ≤ 1 →
      |weightedIntegral μ A B R (fun ω => G₁ ω - G₀ ω) τ / weightedIntegral μ A B R (fun _ => 1) τ -
        (weightedIntegral μ A B R (fun ω => (τ * G₁ ω + (1 - τ) * G₀ ω) * (B ω - A ω)) τ /
            weightedIntegral μ A B R (fun _ => 1) τ -
          (weightedIntegral μ A B R (fun ω => τ * G₁ ω + (1 - τ) * G₀ ω) τ /
              weightedIntegral μ A B R (fun _ => 1) τ) *
            (weightedIntegral μ A B R (fun ω => B ω - A ω) τ /
              weightedIntegral μ A B R (fun _ => 1) τ))| ≤ c) :
    |weightedIntegral μ A B R (fun ω => 1 * G₁ ω + (1 - 1) * G₀ ω) 1 /
        weightedIntegral μ A B R (fun _ => 1) 1 -
      weightedIntegral μ A B R (fun ω => 0 * G₁ ω + (1 - 0) * G₀ ω) 0 /
        weightedIntegral μ A B R (fun _ => 1) 0| ≤ c := by
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Set.Icc (0 : ℝ) 1)
    (x := 0) (y := 1) (C := c)
    (f := fun τ => (weightedIntegral μ A B R G₀ τ +
        τ * weightedIntegral μ A B R (fun ω => G₁ ω - G₀ ω) τ) /
        weightedIntegral μ A B R (fun _ => 1) τ)
    (fun τ _ => (hasDerivAt_weightedMean (μ := μ) hR hRK hG₀ hGK₀ hG₁ hGK₁ hA hB hAM hBM hK hM hZ
      τ).hasDerivWithinAt)
    (fun τ hτ => by
      rw [Real.norm_eq_abs]
      exact hc τ hτ.1 hτ.2)
    (convex_Icc 0 1) (by simp) (by simp)
  rw [weightedIntegral_lineMap (μ := μ) hR hRK hG₀ hGK₀ hG₁ hGK₁ hA hB hAM hBM 1 1 hK,
    weightedIntegral_lineMap (μ := μ) hR hRK hG₀ hGK₀ hG₁ hGK₁ hA hB hAM hBM 0 0 hK]
  simpa using key
end Finite
section Balls
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {r : ℝ → ℝ}
theorem openPolyball_eq_ball (hρ : 0 < ρ) : openPolyball ι ρ = Metric.ball (0 : BondField ι) ρ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.openPolyball_eq_ball <;> assumption
theorem isOpen_openPolyball (hρ : 0 < ρ) : IsOpen (openPolyball ι ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.isOpen_openPolyball <;> assumption
theorem zero_mem_openPolyball (hρ : 0 < ρ) : (0 : BondField ι) ∈ openPolyball ι ρ :=
  fun b => by simpa using hρ
theorem contDiff_radialCutoff_norm (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) :
    ContDiff ℝ 1 fun v : BondVector => r ‖v‖ := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.contDiff_radialCutoff_norm <;> assumption
theorem continuous_radialWeightProd (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) :
    Continuous (radialWeightProd (ι := ι) r) := by
  unfold radialWeightProd
  refine continuous_finset_prod _ fun b _ => ?_
  exact (contDiff_radialCutoff_norm hρ hr).continuous.comp (continuous_apply b)
theorem radialWeightProd_eq_zero (hr : IsRadialCutoff ρ r) (η : BondField ι)
    (h : η ∉ openPolyball ι ρ) : radialWeightProd r η = 0 := by
  simp only [openPolyball, Set.mem_setOf_eq, not_forall, not_lt] at h
  obtain ⟨b, hb⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ b) (hr.zero _ hb)
theorem radialWeightProd_pos (hr : IsRadialCutoff ρ r) (η : BondField ι) (h : η ∈ openPolyball ι ρ) :
    0 < radialWeightProd r η :=
  Finset.prod_pos fun b _ => hr.pos _ (norm_nonneg _) (h b)
theorem hasCompactSupport_radialWeightProd (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) :
    HasCompactSupport (radialWeightProd (ι := ι) r) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
  apply radialWeightProd_eq_zero hr
  intro h
  apply hη
  rw [openPolyball_eq_ball hρ] at h
  exact Metric.ball_subset_closedBall h
theorem measurable_indicator_openPolyball (hρ : 0 < ρ) {f : BondField ι → ℝ}
    (hf : ContinuousOn f (openPolyball ι ρ)) : Measurable ((openPolyball ι ρ).indicator f) := by
  classical
  have h := hf.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
    (isOpen_openPolyball hρ).measurableSet
  have e : (openPolyball ι ρ).piecewise f (fun _ => 0) = (openPolyball ι ρ).indicator f := by
    funext η
    simp [Set.piecewise, Set.indicator]
  rwa [e] at h
theorem abs_indicator_openPolyball_le {f : BondField ι → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ η ∈ openPolyball ι ρ, |f η| ≤ M) (η : BondField ι) :
    |(openPolyball ι ρ).indicator f η| ≤ M := by
  by_cases hη : η ∈ openPolyball ι ρ
  · rw [Set.indicator_of_mem hη]
    exact h η hη
  · rw [Set.indicator_of_notMem hη]
    simpa using hM
theorem integral_ballDensity_eq_weightedIntegral (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r)
    {A B G g Ψ : BondField ι → ℝ} {v : ℝ}
    (hG : ∀ η ∈ openPolyball ι ρ, G η = g η)
    (hΨ : ∀ η ∈ openPolyball ι ρ, Ψ η = v * B η + (1 - v) * A η) :
    ∫ η, g η * ballDensity r Ψ η =
      weightedIntegral (MeasureTheory.volume.restrict (Metric.closedBall (0 : BondField ι) ρ)) A B
        (radialWeightProd r) G v := by
  unfold weightedIntegral
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply integral_congr_ae
    refine Filter.Eventually.of_forall fun η => ?_
    by_cases hη : η ∈ openPolyball ι ρ
    · simp only [ballDensity, segmentExp, hG η hη, hΨ η hη]
      ring
    · simp only [ballDensity, radialWeightProd_eq_zero hr η hη]
      simp
  · intro η hη
    have : η ∉ openPolyball ι ρ := fun h => hη (by
      rw [openPolyball_eq_ball hρ] at h
      exact Metric.ball_subset_closedBall h)
    simp [radialWeightProd_eq_zero hr η this]
end Balls
end SegmentMean
open SegmentMean in
theorem meanDifferenceBoundAlongSegment_holds : MeanDifferenceBoundAlongSegment := by
  intro ι _ _ ρ r A B H₀ H₁ M c hρ hr hA hB hH₀ hH₁ hbd hc
  classical
  set O := openPolyball ι ρ with hO
  have h0 : (0 : BondField ι) ∈ O := zero_mem_openPolyball hρ
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbd 0 h0).1
  set μ := MeasureTheory.volume.restrict (Metric.closedBall (0 : BondField ι) ρ) with hμ
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    ⟨by
      simp only [hμ, MeasureTheory.Measure.restrict_apply_univ]
      exact (isCompact_closedBall (0 : BondField ι) ρ).measure_lt_top⟩
  set R := radialWeightProd (ι := ι) r with hRd
  have hRc : Continuous R := continuous_radialWeightProd hρ hr
  have hRm : Measurable R := hRc.measurable
  obtain ⟨KR, hKR⟩ := (hasCompactSupport_radialWeightProd (ι := ι) hρ hr).exists_bound_of_continuous hRc
  have hRK : ∀ η, |R η| ≤ KR := fun η => by simpa using hKR η
  set A' := O.indicator A
  set B' := O.indicator B
  set G₀ := O.indicator H₀
  set G₁ := O.indicator H₁
  have mA : Measurable A' := measurable_indicator_openPolyball hρ hA
  have mB : Measurable B' := measurable_indicator_openPolyball hρ hB
  have m₀ : Measurable G₀ := measurable_indicator_openPolyball hρ hH₀
  have m₁ : Measurable G₁ := measurable_indicator_openPolyball hρ hH₁
  have bA : ∀ η, |A' η| ≤ M := abs_indicator_openPolyball_le hM fun η h => (hbd η h).1
  have bB : ∀ η, |B' η| ≤ M := abs_indicator_openPolyball_le hM fun η h => (hbd η h).2.1
  have b₀ : ∀ η, |G₀ η| ≤ M := abs_indicator_openPolyball_le hM fun η h => (hbd η h).2.2.1
  have b₁ : ∀ η, |G₁ η| ≤ M := abs_indicator_openPolyball_le hM fun η h => (hbd η h).2.2.2
  have eA : ∀ η ∈ O, A' η = A η := fun η h => Set.indicator_of_mem h _
  have eB : ∀ η ∈ O, B' η = B η := fun η h => Set.indicator_of_mem h _
  have e₀ : ∀ η ∈ O, G₀ η = H₀ η := fun η h => Set.indicator_of_mem h _
  have e₁ : ∀ η ∈ O, G₁ η = H₁ η := fun η h => Set.indicator_of_mem h _
  have hseg : ∀ v, ∀ η ∈ O, segmentInterpolant A B v η = v * B' η + (1 - v) * A' η :=
    fun v η h => by
      simp only [segmentInterpolant, eA η h, eB η h]
  have hden : ∀ (v : ℝ) (Ψ : BondField ι → ℝ),
      (∀ η ∈ O, Ψ η = v * B' η + (1 - v) * A' η) →
      ∫ η, ballDensity r Ψ η = weightedIntegral μ A' B' R (fun _ => 1) v := by
    intro v Ψ h
    have := integral_ballDensity_eq_weightedIntegral (ι := ι) (G := fun _ => 1) (g := fun _ => 1)
      hρ hr (fun _ _ => rfl) h
    simpa using this
  have hpos : ∀ v, 0 < weightedIntegral μ A' B' R (fun _ => 1) v := by
    intro v
    have hrw : weightedIntegral μ A' B' R (fun _ => 1) v =
        ∫ η in Metric.closedBall (0 : BondField ι) ρ, R η * segmentExp A' B' v η := by
      simp [weightedIntegral, hμ]
    rw [hrw, MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsub : O ⊆ Function.support (fun η => R η * segmentExp A' B' v η) ∩
          Metric.closedBall (0 : BondField ι) ρ := by
        intro η hη
        refine ⟨?_, ?_⟩
        · exact (mul_pos (radialWeightProd_pos hr η hη) (Real.exp_pos _)).ne'
        · rw [hO, openPolyball_eq_ball hρ] at hη
          exact Metric.ball_subset_closedBall hη
      refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono hsub)
      exact (isOpen_openPolyball hρ).measure_pos _ ⟨0, h0⟩
    · refine Filter.Eventually.of_forall fun η => mul_nonneg ?_ (Real.exp_pos _).le
      by_cases hη : η ∈ O
      · exact (radialWeightProd_pos hr η hη).le
      · exact (radialWeightProd_eq_zero hr η hη).ge
    · exact integrable_mul_segmentExp (μ := μ) R KR hRm hRK mA mB bA bB v
  have key := abs_weightedMean_sub_le (μ := μ) hRm hRK m₀ b₀ m₁ b₁ mA mB bA bB hM hM hpos (c := c) ?_
  · have h1 : ballExpectation r B H₁ =
        weightedIntegral μ A' B' R (fun ω => 1 * G₁ ω + (1 - 1) * G₀ ω) 1 /
          weightedIntegral μ A' B' R (fun _ => 1) 1 := by
      unfold ballExpectation
      rw [integral_ballDensity_eq_weightedIntegral (A := A') (B := B') (v := 1)
        (G := fun ω => 1 * G₁ ω + (1 - 1) * G₀ ω) hρ hr
        (fun η h => by simp [e₁ η h]) (fun η h => by simp [eB η h]),
        hden 1 B (fun η h => by simp [eB η h])]
    have h2 : ballExpectation r A H₀ =
        weightedIntegral μ A' B' R (fun ω => 0 * G₁ ω + (1 - 0) * G₀ ω) 0 /
          weightedIntegral μ A' B' R (fun _ => 1) 0 := by
      unfold ballExpectation
      rw [integral_ballDensity_eq_weightedIntegral (A := A') (B := B') (v := 0)
        (G := fun ω => 0 * G₁ ω + (1 - 0) * G₀ ω) hρ hr
        (fun η h => by simp [e₀ η h]) (fun η h => by simp [eA η h]),
        hden 0 A (fun η h => by simp [eA η h])]
    rw [h1, h2]
    exact key
  · intro v hv0 hv1
    have hh := hc v hv0 hv1
    have m1 : ballExpectation r (segmentInterpolant A B v) (fun η => H₁ η - H₀ η) =
        weightedIntegral μ A' B' R (fun ω => G₁ ω - G₀ ω) v /
          weightedIntegral μ A' B' R (fun _ => 1) v := by
      unfold ballExpectation
      rw [integral_ballDensity_eq_weightedIntegral (A := A') (B := B') (v := v)
        (G := fun ω => G₁ ω - G₀ ω) hρ hr
        (fun η h => by simp [e₁ η h, e₀ η h]) (hseg v), hden v _ (hseg v)]
    have m2 : ballExpectation r (segmentInterpolant A B v)
        (fun η => segmentInterpolant H₀ H₁ v η * (B η - A η)) =
        weightedIntegral μ A' B' R (fun ω => (v * G₁ ω + (1 - v) * G₀ ω) * (B' ω - A' ω)) v /
          weightedIntegral μ A' B' R (fun _ => 1) v := by
      unfold ballExpectation
      rw [integral_ballDensity_eq_weightedIntegral (A := A') (B := B') (v := v)
        (G := fun ω => (v * G₁ ω + (1 - v) * G₀ ω) * (B' ω - A' ω)) hρ hr
        (fun η h => by simp [segmentInterpolant, e₁ η h, e₀ η h, eA η h, eB η h]) (hseg v),
        hden v _ (hseg v)]
    have m3 : ballExpectation r (segmentInterpolant A B v) (segmentInterpolant H₀ H₁ v) =
        weightedIntegral μ A' B' R (fun ω => v * G₁ ω + (1 - v) * G₀ ω) v /
          weightedIntegral μ A' B' R (fun _ => 1) v := by
      unfold ballExpectation
      rw [integral_ballDensity_eq_weightedIntegral (A := A') (B := B') (v := v)
        (G := fun ω => v * G₁ ω + (1 - v) * G₀ ω) hρ hr
        (fun η h => by simp [segmentInterpolant, e₁ η h, e₀ η h]) (hseg v), hden v _ (hseg v)]
    have m4 : ballExpectation r (segmentInterpolant A B v) (fun η => B η - A η) =
        weightedIntegral μ A' B' R (fun ω => B' ω - A' ω) v /
          weightedIntegral μ A' B' R (fun _ => 1) v := by
      unfold ballExpectation
      rw [integral_ballDensity_eq_weightedIntegral (A := A') (B := B') (v := v)
        (G := fun ω => B' ω - A' ω) hρ hr
        (fun η h => by simp [eA η h, eB η h]) (hseg v), hden v _ (hseg v)]
    unfold ballCovariance at hh
    rw [m1, m2, m3, m4] at hh
    exact hh
end YangMills.Construction.ColdStepAtMirrorFrames
end
