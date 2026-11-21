import Mathlib
set_option autoImplicit false
noncomputable section
open Metric Filter
open scoped Topology
namespace YangMills.Construction.LandauInequality
theorem abs_sub_tangent_le {f f' : ℝ → ℝ} {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hderiv : ∀ t, |t| ≤ ρ → HasDerivAt f (f' t) t) (hlip : ∀ t, |t| ≤ ρ → |f' t - f' 0| ≤ K * |t|)
    {x : ℝ} (hx : |x| ≤ ρ) : |f x - f 0 - x * f' 0| ≤ K * ρ * |x| := by
  set φ : ℝ → ℝ := fun t => f t - t * f' 0 with hφ
  have hconv : Convex ℝ (Set.Icc (-ρ) ρ) := convex_Icc _ _
  have hdφ : ∀ t ∈ Set.Icc (-ρ) ρ, HasDerivWithinAt φ (f' t - f' 0) (Set.Icc (-ρ) ρ) t := by
    intro t ht
    have h1 := hderiv t (abs_le.2 ht)
    have h2 : HasDerivAt (fun t : ℝ => t * f' 0) (f' 0) t := by
      simpa using (hasDerivAt_id t).mul_const (f' 0)
    exact (h1.sub h2).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc (-ρ) ρ, ‖f' t - f' 0‖ ≤ K * ρ := by
    intro t ht
    have h1 := hlip t (abs_le.2 ht)
    have h2 : K * |t| ≤ K * ρ := mul_le_mul_of_nonneg_left (abs_le.2 ht) hK
    rw [Real.norm_eq_abs]
    linarith
  have h0 : (0 : ℝ) ∈ Set.Icc (-ρ) ρ := ⟨by linarith, hρ.le⟩
  have hx' : x ∈ Set.Icc (-ρ) ρ := abs_le.1 hx
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hdφ hb h0 hx'
  simp only [hφ, Real.norm_eq_abs, sub_zero, zero_mul] at h
  have e : f x - x * f' 0 - f 0 = f x - f 0 - x * f' 0 := by ring
  rwa [e] at h
theorem abs_deriv_le_of_nonneg {f f' : ℝ → ℝ} {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hnonneg : ∀ t, |t| ≤ ρ → 0 ≤ f t)
    (hderiv : ∀ t, |t| ≤ ρ → HasDerivAt f (f' t) t) (hlip : ∀ t, |t| ≤ ρ → |f' t - f' 0| ≤ K * |t|) :
    |f' 0| ≤ f 0 / ρ + K * ρ := by
  have hp := abs_sub_tangent_le hρ hK hderiv hlip (x := ρ) (by rw [abs_of_pos hρ])
  have hn := abs_sub_tangent_le hρ hK hderiv hlip (x := -ρ) (by rw [abs_neg, abs_of_pos hρ])
  rw [abs_of_pos hρ] at hp
  rw [abs_neg, abs_of_pos hρ] at hn
  have h1 := hnonneg ρ (by rw [abs_of_pos hρ])
  have h2 := hnonneg (-ρ) (by rw [abs_neg, abs_of_pos hρ])
  have h3 := (abs_le.1 hp).2
  have h4 := (abs_le.1 hn).2
  have hkey : ρ * |f' 0| ≤ f 0 + K * ρ * ρ := by
    rcases abs_cases (f' 0) with ⟨e, _⟩ | ⟨e, _⟩
    · rw [e]
      nlinarith
    · rw [e]
      nlinarith
  rw [div_add' _ _ _ hρ.ne', le_div_iff₀ hρ]
  nlinarith
theorem abs_deriv_sub_le_of_second_diff {f f' : ℝ → ℝ} {r M : ℝ}
    (hderiv : ∀ t, |t| < r → HasDerivAt f (f' t) t)
    (hsecond : ∀ t h₁ h₂, |t| < r → |t + h₁| < r → |t + h₂| < r → |t + h₁ + h₂| < r →
      |f (t + h₁ + h₂) - f (t + h₁) - f (t + h₂) + f t| ≤ M * |h₁| * |h₂|)
    {t h : ℝ} (ht : |t| < r) (hth : |t + h| < r) : |f' (t + h) - f' t| ≤ M * |h| := by
  have h1 := (hasDerivAt_iff_tendsto_slope_zero.1 (hderiv _ hth))
  have h2 := (hasDerivAt_iff_tendsto_slope_zero.1 (hderiv _ ht))
  have h3 := (h1.sub h2).abs
  refine le_of_tendsto h3 ?_
  have hnh : ∀ᶠ x in 𝓝[≠] (0 : ℝ), |t + x| < r ∧ |t + h + x| < r := by
    have c1 : ContinuousAt (fun x : ℝ => |t + x|) 0 := by fun_prop
    have c2 : ContinuousAt (fun x : ℝ => |t + h + x|) 0 := by fun_prop
    have e1 := c1.eventually_lt continuousAt_const (by simpa using ht)
    have e2 := c2.eventually_lt continuousAt_const (by simpa using hth)
    exact (e1.and e2).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnh, self_mem_nhdsWithin] with x hx hx0
  have hx0' : x ≠ 0 := hx0
  have hb := hsecond t h x ht hth hx.1 hx.2
  have e : x⁻¹ • (f (t + h + x) - f (t + h)) - x⁻¹ • (f (t + x) - f t) =
      x⁻¹ * (f (t + h + x) - f (t + h) - f (t + x) + f t) := by
    simp only [smul_eq_mul]
    ring
  rw [e, abs_mul, abs_inv]
  have hxp : 0 < |x| := abs_pos.2 hx0'
  rw [inv_mul_le_iff₀ hxp]
  calc _ ≤ M * |h| * |x| := hb
    _ = |x| * (M * |h|) := by ring
theorem hasDerivAt_re_deriv_of_analytic_extension {g : ℂ → ℂ} {f : ℝ → ℝ} {r : ℝ}
    (hg : ∀ z : ℂ, ‖z‖ < r → AnalyticAt ℂ g z)
    (hf : ∀ t : ℝ, |t| < r → (f t : ℂ) = g t) {t : ℝ} (ht : |t| < r) : HasDerivAt f (deriv g t).re t := by
  have hnt : ‖(t : ℂ)‖ < r := by simpa using ht
  have h1 : HasDerivAt g (deriv g t) (t : ℂ) := (hg _ hnt).differentiableAt.hasDerivAt
  have h2 := h1.real_of_complex
  have hev : ∀ᶠ x in 𝓝 t, (fun x : ℝ => (g x).re) x = f x := by
    have c : ContinuousAt (fun x : ℝ => |x|) t := by fun_prop
    filter_upwards [c.eventually_lt continuousAt_const ht] with x hx
    show (g x).re = f x
    rw [← hf x hx]
    simp
  exact h2.congr_of_eventuallyEq (hev.mono fun x hx => hx.symm)
theorem exists_lipschitz_deriv_of_second_diff {g : ℂ → ℂ} {f : ℝ → ℝ} {r M : ℝ}
    (hg : ∀ z : ℂ, ‖z‖ < r → AnalyticAt ℂ g z)
    (hf : ∀ t : ℝ, |t| < r → (f t : ℂ) = g t)
    (hsecond : ∀ t h₁ h₂ : ℂ, ‖t‖ < r → ‖t + h₁‖ < r → ‖t + h₂‖ < r → ‖t + h₁ + h₂‖ < r →
      ‖g (t + h₁ + h₂) - g (t + h₁) - g (t + h₂) + g t‖ ≤ M * ‖h₁‖ * ‖h₂‖) :
    ∃ f' : ℝ → ℝ, (∀ t, |t| < r → HasDerivAt f (f' t) t) ∧
      ∀ t h, |t| < r → |t + h| < r → |f' (t + h) - f' t| ≤ M * |h| := by
  refine ⟨fun t => (deriv g t).re, fun t ht => hasDerivAt_re_deriv_of_analytic_extension hg hf ht,
    fun t h ht hth => ?_⟩
  refine abs_deriv_sub_le_of_second_diff (f := f) (f' := fun t => (deriv g t).re) (r := r)
    (fun t ht => hasDerivAt_re_deriv_of_analytic_extension hg hf ht)
    (fun t h₁ h₂ h0 h1 h2 h3 => ?_) ht hth
  have c0 := hf _ h0
  have c1 := hf _ h1
  have c2 := hf _ h2
  have c3 := hf _ h3
  have hb := hsecond (t : ℂ) (h₁ : ℂ) (h₂ : ℂ) (by simpa using h0) (by simpa [← Complex.ofReal_add] using h1)
    (by simpa [← Complex.ofReal_add] using h2) (by simpa [← Complex.ofReal_add] using h3)
  have e : g ((t : ℂ) + h₁ + h₂) - g ((t : ℂ) + h₁) - g ((t : ℂ) + h₂) + g t =
      ((f (t + h₁ + h₂) - f (t + h₁) - f (t + h₂) + f t : ℝ) : ℂ) := by
    push_cast at c1 c2 c3 ⊢
    rw [← c1, ← c2, ← c3, ← c0]
  rw [e, Complex.norm_real, Real.norm_eq_abs] at hb
  simpa using hb
theorem norm_deriv_le_of_bounded_on_ball {g : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hg : ∀ z : ℂ, ‖z‖ < r → AnalyticAt ℂ g z)
    (hbound : ∀ z : ℂ, ‖z‖ < r → ‖g z‖ ≤ M) {z : ℂ} (hz : ‖z‖ < r / 2) : ‖deriv g z‖ ≤ M / (r / 4) := by
  have hR : 0 < r / 4 := by positivity
  have hin : ∀ w ∈ closedBall z (r / 4), ‖w‖ < r := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r / 4 := by simpa [dist_eq_norm] using hw
    have h2 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      have := norm_add_le z (w - z)
      simpa using this
    linarith
  have hd : DiffContOnCl ℂ g (ball z (r / 4)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    exact fun w hw => (hg w (hin w hw)).differentiableAt.differentiableWithinAt
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd fun w hw =>
    hbound w (hin w (sphere_subset_closedBall hw))
theorem exists_lipschitz_deriv_of_bounded_extension {g : ℂ → ℂ} {f : ℝ → ℝ} {r M : ℝ} (hr : 0 < r)
    (hg : ∀ z : ℂ, ‖z‖ < r → AnalyticAt ℂ g z)
    (hbound : ∀ z : ℂ, ‖z‖ < r → ‖g z‖ ≤ M) (hf : ∀ t : ℝ, |t| < r → (f t : ℂ) = g t) :
    ∃ f' : ℝ → ℝ, (∀ t, |t| < r → HasDerivAt f (f' t) t) ∧
      ∀ t, |t| < r / 4 → |f' t - f' 0| ≤ M / (r / 4) / (r / 8) * |t| := by
  refine ⟨fun t => (deriv g t).re, fun t ht => hasDerivAt_re_deriv_of_analytic_extension hg hf ht,
    fun t ht => ?_⟩
  set g' := deriv g with hg'
  have han' : ∀ z : ℂ, ‖z‖ < r / 2 → AnalyticAt ℂ g' z := fun z hz =>
    (hg z (by linarith)).deriv
  have hb' : ∀ z : ℂ, ‖z‖ < r / 2 → ‖g' z‖ ≤ M / (r / 4) := fun z hz =>
    norm_deriv_le_of_bounded_on_ball hr hg hbound hz
  have hd2 : ∀ z : ℂ, ‖z‖ < r / 4 → ‖deriv g' z‖ ≤ M / (r / 4) / (r / 8) := by
    intro z hz
    have := norm_deriv_le_of_bounded_on_ball (r := r / 2) (by positivity) han' hb' (z := z) (by linarith)
    have e : r / 2 / 4 = r / 8 := by ring
    rwa [e] at this
  have hconv : Convex ℝ (ball (0 : ℂ) (r / 4)) := convex_ball _ _
  have hfd : ∀ z ∈ ball (0 : ℂ) (r / 4), HasFDerivWithinAt g' ((deriv g' z) • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ))
      (ball (0 : ℂ) (r / 4)) z := by
    intro z hz
    have hz' : ‖z‖ < r / 2 := by
      have : ‖z‖ < r / 4 := by simpa using hz
      linarith
    have h1 : HasDerivAt g' (deriv g' z) z := (han' z hz').differentiableAt.hasDerivAt
    have h2 := h1.hasFDerivAt.restrictScalars ℝ
    refine HasFDerivAt.hasFDerivWithinAt (h2.congr_fderiv ?_)
    ext x
    simp [mul_comm]
  have hbd : ∀ z ∈ ball (0 : ℂ) (r / 4), ‖(deriv g' z) • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)‖ ≤
      M / (r / 4) / (r / 8) := by
    intro z hz
    have h1 := hd2 z (by simpa using hz)
    refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans h1) fun x => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (r / 4) := by simpa using (by positivity : 0 < r / 4)
  have hz : (t : ℂ) ∈ ball (0 : ℂ) (r / 4) := by simpa using ht
  have h := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hfd hbd h0 hz
  have h2 := (Complex.abs_re_le_norm (g' t - g' 0)).trans h
  simpa using h2
end YangMills.Construction.LandauInequality
end
