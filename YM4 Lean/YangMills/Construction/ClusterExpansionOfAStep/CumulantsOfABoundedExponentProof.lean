import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfABoundedExponent
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace YangMills.Construction.Cumulants
variable {Ξ ι E : Type} [MeasurableSpace Ξ] [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
def tiltExponent (u : ι → Ξ → ℝ) (Lf : ι → E →L[ℝ] ℝ) (ξ : Ξ) (θ : E) : ℝ := ∑ i, u i ξ * Lf i θ
def tiltedIntegral (μ : Measure Ξ) (w : Ξ → ℝ) (u : ι → Ξ → ℝ) (Lf : ι → E →L[ℝ] ℝ) (f : Ξ → ℝ)
    (θ : E) : ℝ :=
  ∫ ξ, w ξ * f ξ * Real.exp (tiltExponent u Lf ξ θ) ∂μ
structure BoundedExponentData (μ : Measure Ξ) (w : Ξ → ℝ) (u : ι → Ξ → ℝ) (Lf : ι → E →L[ℝ] ℝ)
    (B : ℝ) : Prop where
  measurable_coeff : ∀ i, Measurable (u i)
  abs_coeff_le : ∀ i ξ, |u i ξ| ≤ B
  abs_exponent_le : ∀ ξ θ, |tiltExponent u Lf ξ θ| ≤ ‖θ‖
  integrable_weight : Integrable w μ
  weight_nonneg : ∀ ξ, 0 ≤ w ξ
  integral_weight_pos : 0 < ∫ ξ, w ξ ∂μ
def BoundedMeasurable (f : Ξ → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ ξ, |f ξ| ≤ C
variable {μ : Measure Ξ} {w : Ξ → ℝ} {u : ι → Ξ → ℝ} {Lf : ι → E →L[ℝ] ℝ} {B : ℝ}
theorem measurable_tiltExponent (h : BoundedExponentData μ w u Lf B) (θ : E) :
    Measurable fun ξ => tiltExponent u Lf ξ θ := by
  unfold tiltExponent
  exact Finset.measurable_fun_sum _ fun i _ => (h.measurable_coeff i).mul_const _
theorem aestronglyMeasurable_integrand (h : BoundedExponentData μ w u Lf B) {f : Ξ → ℝ}
    (hf : Measurable f) (θ : E) :
    AEStronglyMeasurable (fun ξ => w ξ * f ξ * Real.exp (tiltExponent u Lf ξ θ)) μ :=
  (h.integrable_weight.aestronglyMeasurable.mul hf.aestronglyMeasurable).mul
    (Real.measurable_exp.comp (measurable_tiltExponent h θ)).aestronglyMeasurable
theorem norm_integrand_le (h : BoundedExponentData μ w u Lf B) {f : Ξ → ℝ} {C : ℝ}
    (hC : ∀ ξ, |f ξ| ≤ C) (ξ : Ξ) (θ : E) :
    ‖w ξ * f ξ * Real.exp (tiltExponent u Lf ξ θ)‖ ≤ C * Real.exp ‖θ‖ * w ξ := by
  have h1 : Real.exp (tiltExponent u Lf ξ θ) ≤ Real.exp ‖θ‖ :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (h.abs_exponent_le ξ θ))
  have hw := h.weight_nonneg ξ
  have hf := hC ξ
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_pos (Real.exp_pos _)]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hf
  calc w ξ * |f ξ| * Real.exp (tiltExponent u Lf ξ θ) ≤ w ξ * C * Real.exp ‖θ‖ := by gcongr
    _ = C * Real.exp ‖θ‖ * w ξ := by ring
theorem integrable_integrand (h : BoundedExponentData μ w u Lf B) {f : Ξ → ℝ}
    (hf : BoundedMeasurable f) (θ : E) :
    Integrable (fun ξ => w ξ * f ξ * Real.exp (tiltExponent u Lf ξ θ)) μ := by
  obtain ⟨hm, C, hC⟩ := hf
  exact (h.integrable_weight.const_mul (C * Real.exp ‖θ‖)).mono'
    (aestronglyMeasurable_integrand h hm θ)
    (Filter.Eventually.of_forall fun ξ => norm_integrand_le h hC ξ θ)
theorem boundedMeasurable_one : BoundedMeasurable (fun _ : Ξ => (1 : ℝ)) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem BoundedMeasurable.mul {f g : Ξ → ℝ} (hf : BoundedMeasurable f) (hg : BoundedMeasurable g) :
    BoundedMeasurable fun ξ => f ξ * g ξ := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hg
  refine ⟨hm.mul hm', C * C', fun ξ => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC ξ) (hC' ξ) (abs_nonneg _) ((abs_nonneg _).trans (hC ξ))
theorem boundedMeasurable_coeff (h : BoundedExponentData μ w u Lf B) (i : ι) :
    BoundedMeasurable (u i) :=
  ⟨h.measurable_coeff i, B, h.abs_coeff_le i⟩
theorem boundedMeasurable_tiltExponent (h : BoundedExponentData μ w u Lf B) (z : E) :
    BoundedMeasurable fun ξ => tiltExponent u Lf ξ z :=
  ⟨measurable_tiltExponent h z, ‖z‖, fun ξ => h.abs_exponent_le ξ z⟩
theorem abs_tiltedIntegral_le (h : BoundedExponentData μ w u Lf B) {f : Ξ → ℝ}
    (hf : BoundedMeasurable f) {C : ℝ} (hC : ∀ ξ, |f ξ| ≤ C) (θ : E) :
    |tiltedIntegral μ w u Lf f θ| ≤ C * tiltedIntegral μ w u Lf (fun _ => 1) θ := by
  unfold tiltedIntegral
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrable_integrand h boundedMeasurable_one θ).const_mul C)
    (Filter.Eventually.of_forall fun ξ => ?_)
  have hw := h.weight_nonneg ξ
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_pos (Real.exp_pos _)]
  have := hC ξ
  calc w ξ * |f ξ| * Real.exp (tiltExponent u Lf ξ θ)
        ≤ w ξ * C * Real.exp (tiltExponent u Lf ξ θ) := by gcongr
    _ = C * (w ξ * 1 * Real.exp (tiltExponent u Lf ξ θ)) := by ring
theorem tiltedIntegral_one_pos (h : BoundedExponentData μ w u Lf B) (θ : E) :
    0 < tiltedIntegral μ w u Lf (fun _ => 1) θ := by
  have h1 : Real.exp (-‖θ‖) * ∫ ξ, w ξ ∂μ ≤ tiltedIntegral μ w u Lf (fun _ => 1) θ := by
    unfold tiltedIntegral
    rw [← integral_const_mul]
    refine integral_mono (h.integrable_weight.const_mul _)
      (integrable_integrand h boundedMeasurable_one θ) fun ξ => ?_
    have h2 : Real.exp (-‖θ‖) ≤ Real.exp (tiltExponent u Lf ξ θ) :=
      Real.exp_le_exp.mpr (neg_le_of_abs_le (h.abs_exponent_le ξ θ))
    have hw := h.weight_nonneg ξ
    show Real.exp (-‖θ‖) * w ξ ≤ w ξ * 1 * Real.exp (tiltExponent u Lf ξ θ)
    nlinarith
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) h.integral_weight_pos) h1
def exponentForm (u : ι → Ξ → ℝ) (Lf : ι → E →L[ℝ] ℝ) (ξ : Ξ) : E →L[ℝ] ℝ := ∑ i, u i ξ • Lf i
theorem exponentForm_apply (ξ : Ξ) (θ : E) : exponentForm u Lf ξ θ = tiltExponent u Lf ξ θ := by
  simp [exponentForm, tiltExponent]
theorem norm_exponentForm_le (h : BoundedExponentData μ w u Lf B) (ξ : Ξ) :
    ‖exponentForm u Lf ξ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun θ => ?_
  rw [exponentForm_apply, one_mul]
  exact h.abs_exponent_le ξ θ
def tiltedIntegralDeriv (μ : Measure Ξ) (w : Ξ → ℝ) (u : ι → Ξ → ℝ) (Lf : ι → E →L[ℝ] ℝ)
    (f : Ξ → ℝ) (θ : E) : E →L[ℝ] ℝ :=
  ∑ i, tiltedIntegral μ w u Lf (fun ξ => f ξ * u i ξ) θ • Lf i
theorem hasFDerivAt_tiltedIntegral (h : BoundedExponentData μ w u Lf B) {f : Ξ → ℝ}
    (hf : BoundedMeasurable f) (θ : E) :
    HasFDerivAt (tiltedIntegral μ w u Lf f) (tiltedIntegralDeriv μ w u Lf f θ) θ := by
  obtain ⟨hm, C, hC⟩ := id hf
  let F' : E → Ξ → E →L[ℝ] ℝ := fun θ' ξ =>
    ∑ i, (w ξ * (f ξ * u i ξ) * Real.exp (tiltExponent u Lf ξ θ')) • Lf i
  have hF' : ∀ θ' ξ, F' θ' ξ =
      (w ξ * f ξ * Real.exp (tiltExponent u Lf ξ θ')) • exponentForm u Lf ξ := by
    intro θ' ξ
    simp only [F', exponentForm, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
    (F := fun θ' ξ => w ξ * f ξ * Real.exp (tiltExponent u Lf ξ θ')) (F' := F') (x₀ := θ)
    (bound := fun ξ => C * Real.exp (‖θ‖ + 1) * w ξ) (s := Metric.ball θ 1)
    (Metric.ball_mem_nhds θ one_pos)
    (Filter.Eventually.of_forall fun θ' => aestronglyMeasurable_integrand h hm θ')
    (integrable_integrand h hf θ)
    (by
      exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (aestronglyMeasurable_integrand h (hm.mul (h.measurable_coeff i)) θ).smul_const _)
    (Filter.Eventually.of_forall fun ξ θ' hθ' => ?_)
    (h.integrable_weight.const_mul _)
    (Filter.Eventually.of_forall fun ξ θ' _ => ?_)
  · have e1 : (∫ ξ, F' θ ξ ∂μ) = tiltedIntegralDeriv μ w u Lf f θ := by
      simp only [F', tiltedIntegralDeriv, tiltedIntegral]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_smul_const]
      · intro i _
        exact (integrable_integrand h (hf.mul (boundedMeasurable_coeff h i)) θ).smul_const _
    rw [e1] at key
    exact key
  · rw [hF', norm_smul]
    have h1 := norm_integrand_le h hC ξ θ'
    have h2 : ‖θ'‖ ≤ ‖θ‖ + 1 := by
      have := Metric.mem_ball.mp hθ'
      have h3 : ‖θ'‖ - ‖θ‖ ≤ ‖θ' - θ‖ := norm_sub_norm_le _ _
      rw [dist_eq_norm] at this
      linarith
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC ξ)
    have hw := h.weight_nonneg ξ
    calc ‖w ξ * f ξ * Real.exp (tiltExponent u Lf ξ θ')‖ * ‖exponentForm u Lf ξ‖
        ≤ (C * Real.exp ‖θ'‖ * w ξ) * 1 :=
          mul_le_mul h1 (norm_exponentForm_le h ξ) (norm_nonneg _) (by positivity)
      _ ≤ C * Real.exp (‖θ‖ + 1) * w ξ := by
          rw [mul_one]
          gcongr
  · have e0 : HasFDerivAt (fun θ'' => tiltExponent u Lf ξ θ'') (exponentForm u Lf ξ) θ' := by
      have : (fun θ'' => tiltExponent u Lf ξ θ'') = fun θ'' => exponentForm u Lf ξ θ'' := by
        funext θ''
        rw [exponentForm_apply]
      rw [this]
      exact (exponentForm u Lf ξ).hasFDerivAt
    have e1 := (e0.exp).const_mul (w ξ * f ξ)
    rw [hF', ← smul_smul (w ξ * f ξ) (Real.exp (tiltExponent u Lf ξ θ')) (exponentForm u Lf ξ)]
    exact e1
theorem tiltedIntegralDeriv_apply (h : BoundedExponentData μ w u Lf B) {f : Ξ → ℝ}
    (hf : BoundedMeasurable f) (θ z : E) :
    tiltedIntegralDeriv μ w u Lf f θ z =
      tiltedIntegral μ w u Lf (fun ξ => f ξ * tiltExponent u Lf ξ z) θ := by
  have e : ∀ ξ, w ξ * (f ξ * tiltExponent u Lf ξ z) * Real.exp (tiltExponent u Lf ξ θ) =
      ∑ i, Lf i z * (w ξ * (f ξ * u i ξ) * Real.exp (tiltExponent u Lf ξ θ)) := by
    intro ξ
    have e1 : tiltExponent u Lf ξ z = ∑ i, u i ξ * Lf i z := rfl
    rw [e1, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : tiltedIntegral μ w u Lf (fun ξ => f ξ * tiltExponent u Lf ξ z) θ =
      ∑ i, ∫ ξ, Lf i z * (w ξ * (f ξ * u i ξ) * Real.exp (tiltExponent u Lf ξ θ)) ∂μ := by
    rw [← integral_finsetSum]
    · exact integral_congr_ae (Filter.Eventually.of_forall e)
    · intro i _
      exact (integrable_integrand h (hf.mul (boundedMeasurable_coeff h i)) θ).const_mul _
  rw [e2]
  simp only [tiltedIntegralDeriv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, mul_comm]
  rfl
theorem contDiff_tiltedIntegral (h : BoundedExponentData μ w u Lf B) (n : ℕ) :
    ∀ {f : Ξ → ℝ}, BoundedMeasurable f → ContDiff ℝ n (tiltedIntegral μ w u Lf f) := by
  induction n with
  | zero =>
    intro f hf
    exact contDiff_zero.mpr
      (continuous_iff_continuousAt.mpr fun θ => (hasFDerivAt_tiltedIntegral h hf θ).continuousAt)
  | succ n ih =>
    intro f hf
    have hs : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (tiltedIntegral μ w u Lf f) := by
      refine contDiff_succ_iff_hasFDerivAt.mpr
        ⟨tiltedIntegralDeriv μ w u Lf f, ?_, fun θ => hasFDerivAt_tiltedIntegral h hf θ⟩
      unfold tiltedIntegralDeriv
      exact ContDiff.sum fun i _ =>
        (ih (hf.mul (boundedMeasurable_coeff h i))).smul contDiff_const
    exact_mod_cast hs
def tiltedMean (μ : Measure Ξ) (w : Ξ → ℝ) (u : ι → Ξ → ℝ) (Lf : ι → E →L[ℝ] ℝ) (f : Ξ → ℝ)
    (θ : E) : ℝ :=
  tiltedIntegral μ w u Lf f θ / tiltedIntegral μ w u Lf (fun _ => 1) θ
theorem abs_tiltedMean_le (h : BoundedExponentData μ w u Lf B) {f : Ξ → ℝ}
    (hf : BoundedMeasurable f) {C : ℝ} (hC : ∀ ξ, |f ξ| ≤ C) (θ : E) :
    |tiltedMean μ w u Lf f θ| ≤ C := by
  unfold tiltedMean
  rw [abs_div, abs_of_pos (tiltedIntegral_one_pos h θ), div_le_iff₀ (tiltedIntegral_one_pos h θ)]
  exact abs_tiltedIntegral_le h hf hC θ
theorem exists_hasFDerivAt_tiltedMean (h : BoundedExponentData μ w u Lf B) {f : Ξ → ℝ}
    (hf : BoundedMeasurable f) (θ : E) :
    ∃ P' : E →L[ℝ] ℝ, HasFDerivAt (tiltedMean μ w u Lf f) P' θ ∧
      ∀ z, P' z = tiltedMean μ w u Lf (fun ξ => f ξ * tiltExponent u Lf ξ z) θ -
        tiltedMean μ w u Lf f θ * tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ z) θ := by
  have hpos := tiltedIntegral_one_pos h θ
  have hinv := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt θ
    (hasFDerivAt_tiltedIntegral h boundedMeasurable_one θ)
  have hmul := (hasFDerivAt_tiltedIntegral h hf θ).mul hinv
  refine ⟨tiltedIntegral μ w u Lf f θ •
      -(tiltedIntegral μ w u Lf (fun _ => 1) θ ^ 2)⁻¹ • tiltedIntegralDeriv μ w u Lf (fun _ => 1) θ +
      (tiltedIntegral μ w u Lf (fun _ => 1) θ)⁻¹ • tiltedIntegralDeriv μ w u Lf f θ, ?_, fun z => ?_⟩
  · have e : tiltedMean μ w u Lf f =
        tiltedIntegral μ w u Lf f * ((fun y => y⁻¹) ∘ tiltedIntegral μ w u Lf fun _ => 1) := by
      funext y
      simp [tiltedMean, div_eq_mul_inv]
    rw [e]
    exact hmul
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Function.comp_apply]
    rw [tiltedIntegralDeriv_apply h hf, tiltedIntegralDeriv_apply h boundedMeasurable_one]
    simp only [one_mul, tiltedMean]
    field_simp
    ring
theorem exists_hasFDerivAt_log_tiltedIntegral (h : BoundedExponentData μ w u Lf B) (θ : E) :
    ∃ g' : E →L[ℝ] ℝ,
      HasFDerivAt (fun θ => Real.log (tiltedIntegral μ w u Lf (fun _ => 1) θ)) g' θ ∧
      ∀ z, g' z = tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ z) θ := by
  have hpos := tiltedIntegral_one_pos h θ
  refine ⟨_, (hasFDerivAt_tiltedIntegral h boundedMeasurable_one θ).log hpos.ne', fun z => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [tiltedIntegralDeriv_apply h boundedMeasurable_one]
  simp only [one_mul, tiltedMean]
  field_simp
theorem fderiv_clm_apply_const {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {A : E → F →L[ℝ] G} {θ : E}
    (hA : DifferentiableAt ℝ A θ) (v : F) (z : E) :
    fderiv ℝ A θ z v = fderiv ℝ (fun θ' => A θ' v) θ z := by
  have := (hA.hasFDerivAt.clm_apply (hasFDerivAt_const v θ)).fderiv
  rw [this]
  simp
theorem cumulantBounds_holds : CumulantBounds := by
  intro Ξ ι E _ _ _ _ μ w u Lf B hu hb hex hwi hw0 hwp
  have h : BoundedExponentData μ w u Lf B := ⟨hu, hb, hex, hwi, hw0, hwp⟩
  have hg : logLaplaceTransform μ w u Lf =
      fun θ => Real.log (tiltedIntegral μ w u Lf (fun _ => 1) θ) := by
    funext θ
    simp [logLaplaceTransform, tiltedIntegral, tiltExponent]
  rw [hg]
  set g : E → ℝ := fun θ => Real.log (tiltedIntegral μ w u Lf (fun _ => 1) θ) with hgdef
  have hsm : ContDiff ℝ ∞ g := contDiff_infty.mpr fun n =>
    (contDiff_tiltedIntegral h n boundedMeasurable_one).log fun θ =>
      (tiltedIntegral_one_pos h θ).ne'
  have h1 : ContDiff ℝ ∞ (fderiv ℝ g) := hsm.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ g)) := h1.fderiv_right (by simp)
  have d1 : ∀ θ, DifferentiableAt ℝ (fderiv ℝ g) θ := fun θ =>
    (h1.differentiable (by simp)) θ
  have d2 : ∀ θ, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ g)) θ := fun θ =>
    (h2.differentiable (by simp)) θ
  have g1 : ∀ θ v, fderiv ℝ g θ v = tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) θ := by
    intro θ v
    obtain ⟨g', hg', hv⟩ := exists_hasFDerivAt_log_tiltedIntegral h θ
    rw [hg'.fderiv, hv]
  have g2 : ∀ θ w' v, fderiv ℝ (fderiv ℝ g) θ w' v =
      tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ w') θ -
        tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) θ *
          tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w') θ := by
    intro θ w' v
    rw [fderiv_clm_apply_const (d1 θ)]
    have e : (fun θ' => fderiv ℝ g θ' v) = tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) := by
      funext θ'
      exact g1 θ' v
    rw [e]
    obtain ⟨P', hP', hv⟩ := exists_hasFDerivAt_tiltedMean h (boundedMeasurable_tiltExponent h v) θ
    rw [hP'.fderiv, hv]
  have g3 : ∀ θ z w' v, fderiv ℝ (fderiv ℝ (fderiv ℝ g)) θ z w' v =
      (tiltedMean μ w u Lf
          (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ w' * tiltExponent u Lf ξ z) θ -
        tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ w') θ *
          tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ z) θ) -
      ((tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ z) θ -
          tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) θ *
            tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ z) θ) *
          tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w') θ +
        tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) θ *
          (tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w' * tiltExponent u Lf ξ z) θ -
            tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w') θ *
              tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ z) θ)) := by
    intro θ z w' v
    have dw : DifferentiableAt ℝ (fun θ' => fderiv ℝ (fderiv ℝ g) θ' w') θ :=
      (d2 θ).clm_apply (differentiableAt_const _)
    rw [fderiv_clm_apply_const (d2 θ), fderiv_clm_apply_const dw]
    have e : (fun θ' => fderiv ℝ (fderiv ℝ g) θ' w' v) = fun θ' =>
        tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ w') θ' -
          tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) θ' *
            tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w') θ' := by
      funext θ'
      exact g2 θ' w' v
    rw [e]
    obtain ⟨Pa, hPa, ha⟩ := exists_hasFDerivAt_tiltedMean h
      ((boundedMeasurable_tiltExponent h v).mul (boundedMeasurable_tiltExponent h w')) θ
    obtain ⟨Pb, hPb, hb'⟩ := exists_hasFDerivAt_tiltedMean h (boundedMeasurable_tiltExponent h v) θ
    obtain ⟨Pc, hPc, hc⟩ := exists_hasFDerivAt_tiltedMean h (boundedMeasurable_tiltExponent h w') θ
    have := (hPa.sub (hPb.mul hPc)).fderiv
    rw [show (fun θ' =>
          tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ w') θ' -
            tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) θ' *
              tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w') θ') =
        (tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ w') -
          tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) *
            tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w'))
      from rfl, this]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [ha, hb', hc]
    ring
  have bx : ∀ (z : E) ξ, |tiltExponent u Lf ξ z| ≤ ‖z‖ := fun z ξ => h.abs_exponent_le ξ z
  have bxx : ∀ (z z' : E) ξ, |tiltExponent u Lf ξ z * tiltExponent u Lf ξ z'| ≤ ‖z‖ * ‖z'‖ :=
    fun z z' ξ => by
      rw [abs_mul]
      exact mul_le_mul (bx z ξ) (bx z' ξ) (abs_nonneg _) (norm_nonneg _)
  have bxxx : ∀ (z z' z'' : E) ξ,
      |tiltExponent u Lf ξ z * tiltExponent u Lf ξ z' * tiltExponent u Lf ξ z''| ≤
        ‖z‖ * ‖z'‖ * ‖z''‖ :=
    fun z z' z'' ξ => by
      rw [abs_mul]
      exact mul_le_mul (bxx z z' ξ) (bx z'' ξ) (abs_nonneg _) (by positivity)
  have p1 : ∀ θ z, |tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ z) θ| ≤ ‖z‖ := fun θ z =>
    abs_tiltedMean_le h (boundedMeasurable_tiltExponent h z) (bx z) θ
  have p2 : ∀ θ z z',
      |tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ z * tiltExponent u Lf ξ z') θ| ≤
        ‖z‖ * ‖z'‖ := fun θ z z' =>
    abs_tiltedMean_le h ((boundedMeasurable_tiltExponent h z).mul
      (boundedMeasurable_tiltExponent h z')) (bxx z z') θ
  have p3 : ∀ θ z z' z'', |tiltedMean μ w u Lf
      (fun ξ => tiltExponent u Lf ξ z * tiltExponent u Lf ξ z' * tiltExponent u Lf ξ z'') θ| ≤
      ‖z‖ * ‖z'‖ * ‖z''‖ := fun θ z z' z'' =>
    abs_tiltedMean_le h (((boundedMeasurable_tiltExponent h z).mul
      (boundedMeasurable_tiltExponent h z')).mul (boundedMeasurable_tiltExponent h z''))
      (bxxx z z' z'') θ
  refine ⟨hsm, fun θ => ⟨?_, ?_, ?_⟩⟩
  · rw [norm_iteratedFDeriv_one]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [g1, one_mul, Real.norm_eq_abs]
    exact p1 θ v
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w' => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [g2, Real.norm_eq_abs]
    have a1 := p2 θ v w'
    have a2 := p1 θ v
    have a3 := p1 θ w'
    have a4 : |tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) θ *
        tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w') θ| ≤ ‖v‖ * ‖w'‖ := by
      rw [abs_mul]
      exact mul_le_mul a2 a3 (abs_nonneg _) (norm_nonneg _)
    calc _ ≤ _ := abs_sub _ _
      _ ≤ ‖v‖ * ‖w'‖ + ‖v‖ * ‖w'‖ := add_le_add a1 a4
      _ = 2 * ‖w'‖ * ‖v‖ := by ring
  · rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun z => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w' => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [g3, Real.norm_eq_abs]
    set a := tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v) θ
    set b := tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w') θ
    set c := tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ z) θ
    set ab := tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ w') θ
    set ac := tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ z) θ
    set bc := tiltedMean μ w u Lf (fun ξ => tiltExponent u Lf ξ w' * tiltExponent u Lf ξ z) θ
    set abc := tiltedMean μ w u Lf
      (fun ξ => tiltExponent u Lf ξ v * tiltExponent u Lf ξ w' * tiltExponent u Lf ξ z) θ
    have ha : |a| ≤ ‖v‖ := p1 θ v
    have hb2 : |b| ≤ ‖w'‖ := p1 θ w'
    have hc : |c| ≤ ‖z‖ := p1 θ z
    have hab : |ab| ≤ ‖v‖ * ‖w'‖ := p2 θ v w'
    have hac : |ac| ≤ ‖v‖ * ‖z‖ := p2 θ v z
    have hbc : |bc| ≤ ‖w'‖ * ‖z‖ := p2 θ w' z
    have habc : |abc| ≤ ‖v‖ * ‖w'‖ * ‖z‖ := p3 θ v w' z
    have m2 : ∀ {s t S T : ℝ}, |s| ≤ S → |t| ≤ T → |s * t| ≤ S * T := fun h1 h2 => by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    have t1 := m2 hab hc
    have t2 := m2 hac hb2
    have t3 := m2 (m2 ha hc) hb2
    have t4 := m2 ha hbc
    have t5 := m2 ha (m2 hb2 hc)
    have e : (abc - ab * c) - ((ac - a * c) * b + a * (bc - b * c)) =
        abc - ab * c - ac * b + a * c * b - a * bc + a * (b * c) := by ring
    rw [e]
    have tri : ∀ p q r s t v' : ℝ,
        |p - q - r + s - t + v'| ≤ |p| + |q| + |r| + |s| + |t| + |v'| := by
      intro p q r s t v'
      have i1 := abs_add_le (p - q - r + s - t) v'
      have i2 := abs_sub (p - q - r + s) t
      have i3 := abs_add_le (p - q - r) s
      have i4 := abs_sub (p - q) r
      have i5 := abs_sub p q
      linarith
    calc _ ≤ _ := tri _ _ _ _ _ _
      _ ≤ ‖v‖ * ‖w'‖ * ‖z‖ + ‖v‖ * ‖w'‖ * ‖z‖ + ‖v‖ * ‖z‖ * ‖w'‖ + ‖v‖ * ‖z‖ * ‖w'‖ +
          ‖v‖ * (‖w'‖ * ‖z‖) + ‖v‖ * (‖w'‖ * ‖z‖) := by
            gcongr
      _ = 6 * ‖z‖ * ‖w'‖ * ‖v‖ := by ring
end YangMills.Construction.Cumulants
end
