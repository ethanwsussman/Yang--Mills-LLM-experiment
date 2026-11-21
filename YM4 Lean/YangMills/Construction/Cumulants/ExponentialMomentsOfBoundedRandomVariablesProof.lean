import YangMills.Construction.Cumulants.ExponentialMomentsOfBoundedRandomVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Cumulants.ExpMoments
variable {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
private theorem measurable_linearForm {X : Fin m → Ω → ℝ} (hX : ∀ k, Measurable (X k))
    (w : Coordinates.ComplexCoordinates m) : Measurable fun ω => ∑ k, w k * (X k ω : ℂ) :=
  Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (Complex.measurable_ofReal.comp (hX k))
omit [MeasurableSpace Ω] in
private theorem norm_linearForm_le {X : Fin m → Ω → ℝ} {C : ℝ} (hC : ∀ k ω, |X k ω| ≤ C)
    (w : Coordinates.ComplexCoordinates m) (ω : Ω) :
    ‖∑ k, w k * (X k ω : ℂ)‖ ≤ C * ∑ k, ‖w k‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC k ω) (norm_nonneg _)
private theorem continuous_expMomentFn (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Fin m → Ω → ℝ} (hX : ∀ k, Measurable (X k)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k ω, |X k ω| ≤ C) : Continuous (expMomentFn μ X) := by
  rw [continuous_iff_continuousAt]
  intro w₀
  have hsum : Continuous fun w : Coordinates.ComplexCoordinates m => ∑ k, ‖w k‖ := by fun_prop
  have hclose : ∀ᶠ w in 𝓝 w₀, ∑ k, ‖w k‖ < (∑ k, ‖w₀ k‖) + 1 :=
    (hsum.tendsto w₀).eventually_lt_const (by linarith)
  change Tendsto (fun w => ∫ ω, Complex.exp (∑ k, w k * (X k ω : ℂ)) ∂μ) (𝓝 w₀)
    (𝓝 (∫ ω, Complex.exp (∑ k, w₀ k * (X k ω : ℂ)) ∂μ))
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => Real.exp (C * ((∑ k, ‖w₀ k‖) + 1))) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun w =>
      (Complex.measurable_exp.comp (measurable_linearForm hX w)).aestronglyMeasurable
  · filter_upwards [hclose] with w hw
    refine Eventually.of_forall fun ω =>
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    exact (norm_linearForm_le hC w ω).trans (mul_le_mul_of_nonneg_left hw.le hC0)
  · refine Eventually.of_forall fun ω => ?_
    have hcont : Continuous fun w : Coordinates.ComplexCoordinates m =>
        Complex.exp (∑ k, w k * (X k ω : ℂ)) := by fun_prop
    exact hcont.continuousAt
private theorem differentiable_integral_cexp_affine (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F G : Ω → ℂ} (hF : Measurable F) (hG : Measurable G) {R C : ℝ}
    (hFb : ∀ ω, ‖F ω‖ ≤ R) (hGb : ∀ ω, ‖G ω‖ ≤ C) :
    Differentiable ℂ fun t : ℂ => ∫ ω, Complex.exp (F ω + t * G ω) ∂μ := by
  intro t₀
  have hmeas : ∀ t : ℂ, Measurable fun ω => Complex.exp (F ω + t * G ω) := fun t =>
    Complex.measurable_exp.comp (hF.add (measurable_const.mul hG))
  have hbound : ∀ t ∈ Metric.ball t₀ 1, ∀ ω,
      ‖Complex.exp (F ω + t * G ω)‖ ≤ Real.exp (R + (‖t₀‖ + 1) * C) := by
    intro t ht ω
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    have ht' : ‖t‖ ≤ ‖t₀‖ + 1 := by
      have e1 : ‖t - t₀‖ < 1 := by simpa [dist_eq_norm] using ht
      have e2 : ‖t‖ ≤ ‖t₀‖ + ‖t - t₀‖ := norm_le_norm_add_norm_sub' t t₀
      linarith
    calc ‖F ω + t * G ω‖ ≤ ‖F ω‖ + ‖t‖ * ‖G ω‖ := by
          simpa [norm_mul] using norm_add_le (F ω) (t * G ω)
      _ ≤ R + (‖t₀‖ + 1) * C := by
          have := mul_le_mul ht' (hGb ω) (norm_nonneg _) (by positivity)
          linarith [hFb ω]
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t ω => Complex.exp (F ω + t * G ω))
    (F' := fun t ω => Complex.exp (F ω + t * G ω) * G ω) (x₀ := t₀) (s := Metric.ball t₀ 1)
    (bound := fun _ => Real.exp (R + (‖t₀‖ + 1) * C) * C)
    (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun t => (hmeas t).aestronglyMeasurable)
    (Integrable.of_bound (hmeas t₀).aestronglyMeasurable (Real.exp (R + (‖t₀‖ + 1) * C))
      (Eventually.of_forall (hbound t₀ (Metric.mem_ball_self one_pos))))
    ((hmeas t₀).mul hG).aestronglyMeasurable
    (Eventually.of_forall fun ω t ht => by
      rw [norm_mul]
      exact mul_le_mul (hbound t ht ω) (hGb ω) (norm_nonneg _) (Real.exp_pos _).le)
    (integrable_const _)
    (Eventually.of_forall fun ω t _ => by
      have hlin : HasDerivAt (fun t : ℂ => F ω + t * G ω) (G ω) t := by
        simpa using ((hasDerivAt_id t).mul_const (G ω)).const_add (F ω)
      exact hlin.cexp)
  exact hderiv.2.differentiableAt
private theorem linearForm_along_axis (v : Fin m → ℂ) (b : Coordinates.ComplexCoordinates m)
    (j : Fin m) (t : ℂ) :
    ∑ k, (b + t • Coordinates.ComplexCoordinates.stdBasisVector j) k * v k =
      ∑ k, b k * v k + t * v j := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Coordinates.ComplexCoordinates.stdBasisVector]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Pi.single_eq_of_ne hkj]
  · simp
theorem holomorphicAndNormalized_holds : HolomorphicAndNormalized := by
  intro Ω _ μ _ m _ X hXb
  have hX : ∀ k, Measurable (X k) := fun k => (hXb k).measurable
  choose r hr using fun k => (hXb k).bounded
  have hC0 : 0 ≤ ∑ k, |r k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hC : ∀ k ω, |X k ω| ≤ ∑ k, |r k| := fun k ω =>
    (hr k ω).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun k => |r k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)))
  refine ⟨⟨isOpen_univ, ?_, ?_⟩, ?_⟩
  · exact (continuous_pi fun _ => continuous_expMomentFn μ hX hC0 hC).continuousOn
  · intro b _ j
    refine Eventually.of_forall fun t => ?_
    rw [differentiableAt_pi]
    intro _
    have haxis : (fun t : ℂ =>
        expMomentFn μ X (b + t • Coordinates.ComplexCoordinates.stdBasisVector j)) =
        fun t : ℂ => ∫ ω, Complex.exp ((∑ k, b k * (X k ω : ℂ)) + t * (X j ω : ℂ)) ∂μ := by
      funext t
      simp only [expMomentFn]
      congr 1
      funext ω
      rw [linearForm_along_axis (fun k => (X k ω : ℂ)) b j t]
    have hdiff : Differentiable ℂ fun t : ℂ =>
        ∫ ω, Complex.exp ((∑ k, b k * (X k ω : ℂ)) + t * (X j ω : ℂ)) ∂μ :=
      differentiable_integral_cexp_affine μ (measurable_linearForm hX b)
        (Complex.measurable_ofReal.comp (hX j)) (norm_linearForm_le hC b)
        (fun ω => by simpa [Complex.norm_real] using hC j ω)
    rw [← haxis] at hdiff
    exact hdiff t
  · simp [expMomentFn]
end YangMills.Construction.Cumulants.ExpMoments
