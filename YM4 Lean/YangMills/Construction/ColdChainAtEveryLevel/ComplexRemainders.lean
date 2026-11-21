import YangMills.Construction.ColdChainAtEveryLevel.ComplexOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction
namespace ComplexRemainders
open BlockAverages ComplexContours ComplexifiedQuaternions ComplexChainStep LatticePaths BlockLines
  LatticeFractionalIntegration
variable {F : BlockFrame} {j : ℕ}
section Holomorphy
variable {f g : ℂ → ComplexQuat} {ζ : ℂ}
theorem differentiableAt_trace_comp (hf : DifferentiableAt ℂ f ζ) :
    DifferentiableAt ℂ (fun z => (f z).trace) ζ :=
  ((LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).differentiableAt).comp ζ hf
theorem differentiableAt_adjugate_comp (hf : DifferentiableAt ℂ f ζ) :
    DifferentiableAt ℂ (fun z => Matrix.adjugate (f z)) ζ := by
  have hfun : (fun z => Matrix.adjugate (f z)) = fun z => (f z).trace • (1 : ComplexQuat) - f z := by
    funext z
    exact adjugate_eq_trace_smul_sub _
  rw [hfun]
  exact (DifferentiableAt.fun_smul (differentiableAt_trace_comp hf)
    (differentiableAt_const (1 : ComplexQuat))).fun_sub hf
theorem det_eq_trace_mul_adjugate_div_two (a : ComplexQuat) : a.det = (a * Matrix.adjugate a).trace / 2 := by
  rw [Matrix.mul_adjugate, Matrix.trace_smul]
  simp
theorem differentiableAt_det_comp (hf : DifferentiableAt ℂ f ζ) :
    DifferentiableAt ℂ (fun z => (f z).det) ζ := by
  have hfun : (fun z => (f z).det) = fun z => (f z * Matrix.adjugate (f z)).trace / 2 := by
    funext z
    exact det_eq_trace_mul_adjugate_div_two _
  rw [hfun]
  exact (differentiableAt_trace_comp (hf.mul (differentiableAt_adjugate_comp hf))).div_const _
theorem differentiableAt_invSqrt_comp {w : ℂ → ℂ} (hw : DifferentiableAt ℂ w ζ) (hs : w ζ ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun z => invSqrt (w z)) ζ := by
  unfold invSqrt
  exact ((differentiableAt_const _).mul (hw.clog hs)).cexp
theorem differentiableAt_principalSqrt_comp {w : ℂ → ℂ} (hw : DifferentiableAt ℂ w ζ)
    (hs : w ζ ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun z => principalSqrt (w z)) ζ := by
  unfold principalSqrt
  exact ((differentiableAt_const _).mul (hw.clog hs)).cexp
theorem differentiableAt_unitPart_comp (hf : DifferentiableAt ℂ f ζ) (h0 : f ζ ≠ 0)
    (hs : (f ζ).det ∈ Complex.slitPlane) : DifferentiableAt ℂ (fun z => unitPart (f z)) ζ := by
  have hev : (fun z => unitPart (f z)) =ᶠ[nhds ζ] fun z => invSqrt (f z).det • f z := by
    have hne : ∀ᶠ z in nhds ζ, f z ≠ 0 := hf.continuousAt.eventually_ne h0
    filter_upwards [hne] with z hz
    rw [unitPart, if_neg hz]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  exact (differentiableAt_invSqrt_comp (differentiableAt_det_comp hf) hs).smul hf
theorem differentiableAt_conjByUnit_comp (g0 : UnitQuaternion) (hf : DifferentiableAt ℂ f ζ) :
    DifferentiableAt ℂ (fun z => conjByUnit g0 (f z)) ζ := by
  unfold conjByUnit
  exact ((differentiableAt_const _).mul hf).mul (differentiableAt_const _)
theorem differentiableAt_purePart_comp (hf : DifferentiableAt ℂ f ζ) :
    DifferentiableAt ℂ (fun z => purePart (f z)) ζ := by
  unfold purePart
  exact (hf.fun_sub (differentiableAt_adjugate_comp hf)).const_smul (1 / 2 : ℂ)
end Holomorphy
section Cauchy
variable {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem norm_sub_le_of_bound_on_lines {N : V → ℝ} (hNadd : ∀ a b, N (a + b) ≤ N a + N b)
    (hNsmul : ∀ (z : ℂ) a, N (z • a) = ‖z‖ * N a) {G : V → E} {ε M : ℝ} (hε : 0 < ε) (y e : V)
    (hhol : ∀ z : ℂ, N (y + z • e) < ε → DifferentiableAt ℂ (fun w : ℂ => G (y + w • e)) z)
    (hM : ∀ z : ℂ, N (y + z • e) < ε → ‖G (y + z • e)‖ ≤ M) (ρ : ℝ) (hρ : 0 < ρ)
    (hin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → N (y + (s : ℂ) • e) + ρ < ε) :
    ‖G (y + e) - G y‖ ≤ M / ρ * N e := by
  have key : ∀ δ : ℝ, 0 < δ → ‖G (y + e) - G y‖ ≤ M / ρ * (N e + δ) := by
    intro δ hδ
    have hN0 : 0 ≤ N e := by
      have h1 := hNsmul 0 e
      have h2 := hNadd e (-e)
      have h3 := hNsmul (-1) e
      simp only [zero_smul, norm_zero, zero_mul, add_neg_cancel, neg_smul, one_smul, norm_neg, norm_one,
        one_mul] at h1 h3
      rw [add_neg_cancel, h1, h3] at h2
      linarith
    set m : ℝ := N e + δ with hm
    have hmpos : 0 < m := by positivity
    set R : ℝ := ρ / m with hR
    have hRpos : 0 < R := by positivity
    set f : ℂ → E := fun w => G (y + w • e) with hf
    have hdom : ∀ z : ℂ, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖z - s‖ ≤ R → N (y + z • e) < ε := by
      intro z s hs0 hs1 hz
      have e1 : y + z • e = (y + (s : ℂ) • e) + (z - s) • e := by
        rw [sub_smul]
        abel
      rw [e1]
      refine lt_of_le_of_lt (hNadd _ _) ?_
      rw [hNsmul]
      have h1 : ‖z - s‖ * N e ≤ R * m := by
        refine mul_le_mul hz ?_ hN0 hRpos.le
        linarith
      have h2 : R * m = ρ := by
        rw [hR]
        field_simp
      have := hin s hs0 hs1
      linarith
    have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖deriv f s‖ ≤ M / R := by
      intro s hs
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos ?_ ?_
      · refine DifferentiableOn.diffContOnCl_ball (U := Metric.closedBall (s : ℂ) R) ?_ subset_rfl
        intro z hz
        have hz' : ‖z - s‖ ≤ R := by simpa [dist_eq_norm] using hz
        exact (hhol z (hdom z s hs.1 hs.2 hz')).differentiableWithinAt
      · intro z hz
        have hz' : ‖z - s‖ ≤ R := by
          have : ‖z - s‖ = R := by simpa [dist_eq_norm] using hz
          exact this.le
        exact hM z (hdom z s hs.1 hs.2 hz')
    have hd1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun x : ℝ => f (x : ℂ)) (deriv f s) (Set.Icc 0 1) s := by
      intro s hsI
      have hdz : DifferentiableAt ℂ f (s : ℂ) := hhol s (hdom s s hsI.1 hsI.2 (by simpa using hRpos.le))
      have h1 : HasDerivAt (fun x : ℝ => ((id x : ℝ) : ℂ)) ((1 : ℝ) : ℂ) s := (hasDerivAt_id s).ofReal_comp
      have h2 := HasDerivAt.scomp (𝕜' := ℂ) s (h := fun x : ℝ => ((id x : ℝ) : ℂ)) hdz.hasDerivAt h1
      have h3 : HasDerivAt (fun x : ℝ => f (x : ℂ)) (deriv f s) s := by
        simpa [Function.comp_def] using h2
      exact h3.hasDerivWithinAt
    have hfin := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun x : ℝ => f (x : ℂ))
      (f' := fun x : ℝ => deriv f x) (C := M / R) (a := 0) (b := 1) hd1
      (fun s hs => hderiv s ⟨hs.1, hs.2.le⟩) 1 (Set.right_mem_Icc.2 zero_le_one)
    simp only [hf, Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul, add_zero, sub_zero,
      mul_one] at hfin
    have e2 : M / R = M / ρ * m := by
      rw [hR]
      field_simp
    rw [e2] at hfin
    exact hfin
  have hMρ : 0 ≤ M / ρ ∨ M / ρ < 0 := le_or_gt 0 (M / ρ)
  refine le_of_forall_pos_le_add fun ε' hε' => ?_
  rcases hMρ with h | h
  · rcases h.eq_or_lt with h0 | h0
    · have := key 1 one_pos
      rw [← h0, zero_mul] at this
      rw [← h0, zero_mul, zero_add]
      linarith
    · have := key (ε' / (M / ρ)) (by positivity)
      have e3 : M / ρ * (N e + ε' / (M / ρ)) = M / ρ * N e + ε' := by
        rw [mul_add, mul_div_cancel₀ _ h0.ne']
      rw [e3] at this
      exact this
  · have h1 := key 1 one_pos
    have hN0 : 0 ≤ N e := by
      have h1 := hNsmul 0 e
      have h2 := hNadd e (-e)
      have h3 := hNsmul (-1) e
      simp only [zero_smul, norm_zero, zero_mul, neg_smul, one_smul, norm_neg, norm_one, one_mul] at h1 h3
      rw [add_neg_cancel, h1, h3] at h2
      linarith
    have : M / ρ * (N e + 1) < 0 := mul_neg_of_neg_of_pos h (by linarith)
    exact absurd (norm_nonneg _) (not_le.2 (lt_of_le_of_lt h1 this))
end Cauchy
section Quadratic
variable {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
structure QuadraticBoundOnBall (N : V → ℝ) (G : V → E) (K σ ε : ℝ) : Prop where
  triangle : ∀ a b, N (a + b) ≤ N a + N b
  homogeneous : ∀ (z : ℂ) a, N (z • a) = ‖z‖ * N a
  holomorphic : ∀ (y e : V) (z : ℂ), N (y + z • e) < ε → DifferentiableAt ℂ (fun w : ℂ => G (y + w • e)) z
  bound : ∀ y, N y < ε → ‖G y‖ ≤ K * (N y ^ 2 + σ * N y)
variable {N : V → ℝ} {G : V → E} {K σ ε : ℝ}
theorem QuadraticBoundOnBall.nonneg (h : QuadraticBoundOnBall N G K σ ε) (a : V) : 0 ≤ N a := by
  have h1 := h.homogeneous 0 a
  have h2 := h.triangle a (-a)
  have h3 := h.homogeneous (-1) a
  simp only [zero_smul, norm_zero, zero_mul, neg_smul, one_smul, norm_neg, norm_one, one_mul] at h1 h3
  rw [add_neg_cancel, h1, h3] at h2
  linarith
theorem QuadraticBoundOnBall.norm_sub_le (h : QuadraticBoundOnBall N G K σ ε) (hK : 0 ≤ K) (hσ : 0 < σ)
    {t : ℝ} (ht : 0 ≤ t) (hsmall : 3 * (t + σ) < ε) {y y' : V} (hy : N y ≤ t) (hy' : N y' ≤ t) :
    ‖G y' - G y‖ ≤ 12 * K * (t + σ) * N (y' - y) := by
  set ρ := t + σ with hρd
  have hρ : 0 < ρ := by positivity
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → N (y + (s : ℂ) • (y' - y)) ≤ t := by
    intro s h0 h1
    have e : y + (s : ℂ) • (y' - y) = ((1 - s : ℝ) : ℂ) • y + (s : ℂ) • y' := by
      push_cast
      module
    rw [e]
    refine (h.triangle _ _).trans ?_
    rw [h.homogeneous, h.homogeneous, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    nlinarith
  have hball : ∀ z : ℂ, N (y + z • (y' - y)) < t + 2 * ρ →
      ‖G (y + z • (y' - y))‖ ≤ 12 * K * ρ ^ 2 := by
    intro z hz
    have h1 := h.bound _ (lt_of_lt_of_le hz (by linarith))
    have h2 := h.nonneg (y + z • (y' - y))
    refine h1.trans ?_
    have h5 : N (y + z • (y' - y)) ^ 2 + σ * N (y + z • (y' - y)) ≤ 12 * ρ ^ 2 := by
      nlinarith
    calc _ ≤ K * (12 * ρ ^ 2) := mul_le_mul_of_nonneg_left h5 hK
      _ = _ := by ring
  have hlin := norm_sub_le_of_bound_on_lines (N := N) (G := G) h.triangle h.homogeneous (ε := t + 2 * ρ)
    (M := 12 * K * ρ ^ 2) (by positivity) y (y' - y)
    (fun z hz => h.holomorphic y (y' - y) z (lt_of_lt_of_le hz (by linarith))) hball ρ hρ
    (fun s h0 h1 => by
      have := hseg s h0 h1
      linarith)
  have e1 : y + (y' - y) = y' := by abel
  rw [e1] at hlin
  have e2 : 12 * K * ρ ^ 2 / ρ = 12 * K * ρ := by
    field_simp
  rw [e2] at hlin
  exact hlin
theorem QuadraticBoundOnBall.norm_second_diff_le (h : QuadraticBoundOnBall N G K σ ε) (hK : 0 ≤ K)
    (hσ : 0 < σ) (hσε : 24 * σ < ε) {y e₁ e₂ : V} {t : ℝ} (ht : 0 ≤ t) (htε : 24 * t < ε) (hy : N y ≤ t)
    (h1 : N e₁ ≤ t) (h2 : N e₂ ≤ t) :
    ‖G (y + e₁ + e₂) - G (y + e₁) - G (y + e₂) + G y‖ ≤ 64 * K * N e₁ * N e₂ := by
  have hεpos : 0 < ε := by linarith
  set ρ := ε / 16 with hρd
  have hρ : 0 < ρ := by positivity
  set G₁ : V → E := fun v => G (v + e₁) - G v with hG₁
  have hn1 := h.nonneg e₁
  have hball : ∀ z : ℂ, N (y + z • e₂) < t + 2 * ρ → ‖G₁ (y + z • e₂)‖ ≤ 4 * K * ε * N e₁ := by
    intro z hz
    have hv := hz.le
    have hv2 : N (y + z • e₂ + e₁) ≤ 2 * t + 2 * ρ := by
      refine (h.triangle _ _).trans ?_
      linarith
    have hl := h.norm_sub_le hK hσ (t := 2 * t + 2 * ρ) (by positivity)
      (by rw [hρd]; linarith) (y := y + z • e₂) (y' := y + z • e₂ + e₁) (by linarith) hv2
    have e : y + z • e₂ + e₁ - (y + z • e₂) = e₁ := by abel
    rw [e] at hl
    refine hl.trans ?_
    have h3 : 12 * K * (2 * t + 2 * ρ + σ) ≤ 4 * K * ε := by
      have : 3 * (2 * t + 2 * ρ + σ) ≤ ε := by
        rw [hρd]
        linarith
      nlinarith
    exact mul_le_mul_of_nonneg_right h3 hn1
  have hhol : ∀ z : ℂ, N (y + z • e₂) < t + 2 * ρ →
      DifferentiableAt ℂ (fun w : ℂ => G₁ (y + w • e₂)) z := by
    intro z hz
    have h1' : N ((y + e₁) + z • e₂) < ε := by
      have e : (y + e₁) + z • e₂ = (y + z • e₂) + e₁ := by abel
      rw [e]
      refine lt_of_le_of_lt (h.triangle _ _) ?_
      rw [hρd] at hz
      linarith
    have h2' : N (y + z • e₂) < ε := by
      rw [hρd] at hz
      linarith
    have d1 := h.holomorphic (y + e₁) e₂ z h1'
    have d2 := h.holomorphic y e₂ z h2'
    have e : (fun w : ℂ => G₁ (y + w • e₂)) = fun w => G ((y + e₁) + w • e₂) - G (y + w • e₂) := by
      funext w
      simp only [hG₁]
      congr 2
      abel
    rw [e]
    exact d1.fun_sub d2
  have hlin := norm_sub_le_of_bound_on_lines (N := N) (G := G₁) h.triangle h.homogeneous (ε := t + 2 * ρ)
    (M := 4 * K * ε * N e₁) (by positivity) y e₂ hhol hball ρ hρ (fun s h0 h1' => by
      have h3 := h.triangle y ((s : ℂ) • e₂)
      rw [h.homogeneous, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at h3
      have h4 : s * N e₂ ≤ t := by
        have := h.nonneg e₂
        nlinarith
      have h5 : t < ρ := by
        rw [hρd]
        linarith
      linarith)
  have e1 : G₁ (y + e₂) - G₁ y = G (y + e₁ + e₂) - G (y + e₁) - G (y + e₂) + G y := by
    simp only [hG₁]
    rw [show y + e₂ + e₁ = y + e₁ + e₂ by abel]
    abel
  rw [e1] at hlin
  have e2 : 4 * K * ε * N e₁ / ρ = 64 * K * N e₁ := by
    rw [hρd]
    field_simp
    ring
  rw [e2] at hlin
  exact hlin
end Quadratic
section Lifts
def liftedField (R : F.GaugeField j) (y : F.Site j → Fin 4 → ComplexQuat) : F.ComplexField j :=
  fun x i => unitPart (1 + y x i) * ofUnit (R x i)
theorem linkDeviation_liftedField (R : F.GaugeField j) (y : F.Site j → Fin 4 → ComplexQuat) (x : F.Site j)
    (i : Fin 4) : linkDeviation (liftedField R y) R x i = unitPart (1 + y x i) - 1 := by
  simp only [linkDeviation, liftedField, mul_assoc, ofUnit_mul_inv, mul_one]
def bondHullSum (c : F.Site (j + 1) × Fin 4) (f : F.Site j → Fin 4 → ℝ) : ℝ :=
  (∑ h ∈ centredCube F.blockSide, ∑ k : Fin 4, if h + Pi.single k 1 ∈ centredCube F.blockSide then
      f (refineSite c.1 + siteOfCoords j h) k +
        f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else 0) +
    ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, f (lineBond c h r).1 (lineBond c h r).2
def bondHullNorm (c : F.Site (j + 1) × Fin 4) (y : F.Site j → Fin 4 → ComplexQuat) : ℝ :=
  bondHullSum c fun x i => ‖y x i‖
theorem bondHullSum_nonneg (c : F.Site (j + 1) × Fin 4) {f : F.Site j → Fin 4 → ℝ} (hf : ∀ x i, 0 ≤ f x i) :
    0 ≤ bondHullSum c f := by
  refine add_nonneg (Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun k _ => ?_)
    (Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun r _ => hf _ _)
  split_ifs
  · exact add_nonneg (hf _ _) (hf _ _)
  · exact le_rfl
theorem bondHullSum_mono (c : F.Site (j + 1) × Fin 4) {f g : F.Site j → Fin 4 → ℝ}
    (hfg : ∀ x i, f x i ≤ g x i) : bondHullSum c f ≤ bondHullSum c g := by
  refine add_le_add (Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun k _ => ?_)
    (Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun r _ => hfg _ _)
  split_ifs
  · exact add_le_add (hfg _ _) (hfg _ _)
  · exact le_rfl
theorem bondHullSum_add (c : F.Site (j + 1) × Fin 4) (f g : F.Site j → Fin 4 → ℝ) :
    bondHullSum c (fun x i => f x i + g x i) = bondHullSum c f + bondHullSum c g := by
  unfold bondHullSum
  have e1 : ∀ h k, (if h + Pi.single k 1 ∈ centredCube F.blockSide then
      f (refineSite c.1 + siteOfCoords j h) k + g (refineSite c.1 + siteOfCoords j h) k +
        (f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k +
          g (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k)
      else (0 : ℝ)) =
      (if h + Pi.single k 1 ∈ centredCube F.blockSide then
        f (refineSite c.1 + siteOfCoords j h) k +
          f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else 0) +
      (if h + Pi.single k 1 ∈ centredCube F.blockSide then
        g (refineSite c.1 + siteOfCoords j h) k +
          g (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else 0) := by
    intro h k
    split_ifs <;> ring
  simp only [e1, Finset.sum_add_distrib]
  ring
theorem bondHullSum_smul (c : F.Site (j + 1) × Fin 4) (a : ℝ) (f : F.Site j → Fin 4 → ℝ) :
    bondHullSum c (fun x i => a * f x i) = a * bondHullSum c f := by
  unfold bondHullSum
  have e1 : ∀ h k, (if h + Pi.single k 1 ∈ centredCube F.blockSide then
      a * f (refineSite c.1 + siteOfCoords j h) k +
        a * f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else (0 : ℝ)) =
      a * (if h + Pi.single k 1 ∈ centredCube F.blockSide then
        f (refineSite c.1 + siteOfCoords j h) k +
          f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else 0) := by
    intro h k
    split_ifs <;> ring
  simp only [e1, mul_add, Finset.mul_sum]
theorem bondHullNorm_add_le (c : F.Site (j + 1) × Fin 4) (a b : F.Site j → Fin 4 → ComplexQuat) :
    bondHullNorm c (a + b) ≤ bondHullNorm c a + bondHullNorm c b := by
  unfold bondHullNorm
  rw [← bondHullSum_add]
  exact bondHullSum_mono c fun x i => norm_add_le _ _
theorem bondHullNorm_smul (c : F.Site (j + 1) × Fin 4) (z : ℂ) (a : F.Site j → Fin 4 → ComplexQuat) :
    bondHullNorm c (z • a) = ‖z‖ * bondHullNorm c a := by
  unfold bondHullNorm
  rw [← bondHullSum_smul]
  congr 1
  funext x i
  simp [norm_smul]
theorem le_bondHullSum_of_block (c : F.Site (j + 1) × Fin 4) {f : F.Site j → Fin 4 → ℝ}
    (hf : ∀ x i, 0 ≤ f x i) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (k : Fin 4)
    (hk : h + Pi.single k 1 ∈ centredCube F.blockSide) :
    f (refineSite c.1 + siteOfCoords j h) k ≤ bondHullSum c f ∧
      f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k ≤ bondHullSum c f := by
  have h1 : (if h + Pi.single k 1 ∈ centredCube F.blockSide then
      f (refineSite c.1 + siteOfCoords j h) k +
        f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else 0) ≤
      ∑ h ∈ centredCube F.blockSide, ∑ k : Fin 4, if h + Pi.single k 1 ∈ centredCube F.blockSide then
        f (refineSite c.1 + siteOfCoords j h) k +
          f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else 0 := by
    have hnn : ∀ h' (k' : Fin 4), 0 ≤ (if h' + Pi.single k' 1 ∈ centredCube F.blockSide then
        f (refineSite c.1 + siteOfCoords j h') k' +
          f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h') k' else (0 : ℝ)) := by
      intro h' k'
      split_ifs
      · exact add_nonneg (hf _ _) (hf _ _)
      · exact le_rfl
    refine le_trans ?_ (Finset.single_le_sum (f := fun h' => ∑ k : Fin 4,
        if h' + Pi.single k 1 ∈ centredCube F.blockSide then
        f (refineSite c.1 + siteOfCoords j h') k +
          f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h') k else 0)
      (fun h' _ => Finset.sum_nonneg fun k' _ => hnn h' k') hh)
    exact Finset.single_le_sum (f := fun k' => if h + Pi.single k' 1 ∈ centredCube F.blockSide then
        f (refineSite c.1 + siteOfCoords j h) k' +
          f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k' else 0)
      (fun k' _ => hnn h k') (Finset.mem_univ k)
  rw [if_pos hk] at h1
  have h2 : 0 ≤ ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      f (lineBond c h r).1 (lineBond c h r).2 :=
    Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun r _ => hf _ _
  have h3 := hf (refineSite c.1 + siteOfCoords j h) k
  have h4 := hf (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k
  unfold bondHullSum
  constructor <;> linarith
theorem le_bondHullSum_of_line (c : F.Site (j + 1) × Fin 4) {f : F.Site j → Fin 4 → ℝ}
    (hf : ∀ x i, 0 ≤ f x i) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) {r : ℕ}
    (hr : r ∈ Finset.range F.blockSide) :
    f (lineBond c h r).1 (lineBond c h r).2 ≤ bondHullSum c f := by
  have h1 : f (lineBond c h r).1 (lineBond c h r).2 ≤
      ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, f (lineBond c h r).1 (lineBond c h r).2 := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun h' => ∑ r ∈ Finset.range F.blockSide, f (lineBond c h' r).1 (lineBond c h' r).2)
      (fun h' _ => Finset.sum_nonneg fun r _ => hf _ _) hh)
    exact Finset.single_le_sum (f := fun r' => f (lineBond c h r').1 (lineBond c h r').2)
      (fun r' _ => hf _ _) hr
  have h2 : 0 ≤ ∑ h ∈ centredCube F.blockSide, ∑ k : Fin 4,
      if h + Pi.single k 1 ∈ centredCube F.blockSide then
      f (refineSite c.1 + siteOfCoords j h) k +
        f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k else 0 := by
    refine Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun k _ => ?_
    split_ifs
    · exact add_nonneg (hf _ _) (hf _ _)
    · exact le_rfl
  unfold bondHullSum
  linarith
theorem contoursNearReal_liftedField (hodd : Odd F.blockSide) {R : F.GaugeField j}
    {y : F.Site j → Fin 4 → ComplexQuat} {c : F.Site (j + 1) × Fin 4} {σ : ℝ} (hy : bondHullNorm c y ≤ 1 / 32)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ) :
    ContoursNearReal (liftedField R y) R (2 * bondHullNorm c y) σ c := by
  have hL : 1 ≤ F.blockSide := hodd.pos
  have hgood : ∀ x i, ‖y x i‖ ≤ bondHullNorm c y →
      BondNearReal (liftedField R y) R (2 * bondHullNorm c y) x i := by
    intro x i hxi
    have hb : ‖y x i‖ ≤ 1 / 32 := hxi.trans hy
    have h1 := norm_unitPart_one_add_sub_le (hb.trans (by norm_num))
    have h2 := norm_purePart_le (y x i)
    have hn := norm_nonneg (y x i)
    constructor
    · rw [linkDeviation_liftedField]
      have e : unitPart (1 + y x i) - 1 = (unitPart (1 + y x i) - 1 - purePart (y x i)) + purePart (y x i) := by
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      nlinarith
    · rw [liftedField, Matrix.det_mul, det_ofUnit, mul_one]
      exact det_unitPart (det_one_add_ne_zero_of_norm_lt_one (by linarith))
  have hnn : ∀ x i, (0 : ℝ) ≤ ‖y x i‖ := fun _ _ => norm_nonneg _
  refine ⟨?_, ?_, ?_, href⟩
  · intro h hh π
    exact pathNearReal_axisPath _ hL (fun v hv k hk =>
      hgood _ _ (le_bondHullSum_of_block c hnn hv k hk).1) hh π
  · intro h hh
    exact pathNearReal_replicate _ _ _ fun r hr => hgood _ _ (le_bondHullSum_of_line c hnn hh hr)
  · intro h hh π
    exact pathNearReal_axisPath _ hL (fun v hv k hk =>
      hgood _ _ (le_bondHullSum_of_block c hnn hv k hk).2) hh π
end Lifts
section Remainders
def liftedBondMean (R : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (y : F.Site j → Fin 4 → ComplexQuat) :
    ComplexQuat :=
  complexGaugedContourAverage (liftedField R y) (complexBalancingGauge (liftedField R y) R) c
def unitRemainder (R : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (y : F.Site j → Fin 4 → ComplexQuat) :
    ComplexQuat :=
  unitPart (liftedBondMean R c y) * ofUnit (polarUnit (contourAverage R c))⁻¹ - 1 -
    purePart (transportedAverage R y c)
def sqrtRemainder (R : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) (y : F.Site j → Fin 4 → ComplexQuat) : ℂ :=
  principalSqrt (liftedBondMean R c y).det - ((‖contourAverage R c‖ : ℝ) : ℂ)
def purePartLinear : ComplexQuat →ₗ[ℂ] ComplexQuat where
  toFun := purePart
  map_add' := purePart_add
  map_smul' z a := purePart_smul z a
theorem purePart_purePart (a : ComplexQuat) : purePart (purePart a) = purePart a := by
  have h := adjugate_purePart a
  rw [purePart, h, sub_neg_eq_add, ← two_smul ℂ (purePart a), smul_smul]
  norm_num
theorem purePart_transportedAverage (R : F.GaugeField j) (f : F.Site j → Fin 4 → ComplexQuat)
    (c : F.Site (j + 1) × Fin 4) :
    purePart (transportedAverage R f c) = transportedAverage R (fun x i => purePart (f x i)) c := by
  rw [transportedAverage]
  have := map_blockContourMean (F := F) purePartLinear (fun h π => ∑ r ∈ Finset.range F.blockSide,
    conjByUnit (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
      (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2))
  refine this.trans ?_
  rw [transportedAverage]
  congr 1
  funext h π
  rw [map_sum]
  exact Finset.sum_congr rfl fun r _ => purePart_conjByUnit _ _
theorem transportedAverage_sub (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ComplexQuat)
    (c : F.Site (j + 1) × Fin 4) :
    transportedAverage R (fun x i => f x i - g x i) c = transportedAverage R f c - transportedAverage R g c := by
  simp only [transportedAverage, ← blockContourMean_sub, ← Finset.sum_sub_distrib, conjByUnit_sub]
theorem lineBlockAverage_le (hodd : Odd F.blockSide) {f : F.Site j → Fin 4 → ℝ} {c : F.Site (j + 1) × Fin 4}
    {b : ℝ} (hf : ∀ h ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide,
      f (lineBond c h r).1 (lineBond c h r).2 ≤ b) :
    lineBlockAverage f c ≤ F.blockSide * b := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have h1 : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      f (lineBond c h r).1 (lineBond c h r).2 ≤
      ∑ h ∈ centredCube F.blockSide, (F.blockSide : ℝ) * b := by
    refine Finset.sum_le_sum fun h hh => ?_
    refine (Finset.sum_le_card_nsmul _ _ b (hf h hh)).trans ?_
    simp
  rw [Finset.sum_const, card_centredCube hodd] at h1
  have e : lineBlockAverage f c = 1 / (F.blockSide : ℝ) ^ 4 *
      ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        f (lineBond c h r).1 (lineBond c h r).2 := rfl
  rw [e]
  calc _ ≤ 1 / (F.blockSide : ℝ) ^ 4 * ((F.blockSide ^ 4) • ((F.blockSide : ℝ) * b)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = F.blockSide * b := by
        rw [nsmul_eq_mul]
        push_cast
        field_simp
theorem remainder_bounds (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {y : F.Site j → Fin 4 → ComplexQuat} {c : F.Site (j + 1) × Fin 4} {σ : ℝ} (hσ : σ ≤ 1 / 64)
    (hy : 8 * (F.blockSide : ℝ) * bondHullNorm c y ≤ 1 / 1024)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ) :
    0 < (liftedBondMean R c y).det.re ∧
    ‖unitRemainder R c y‖ ≤
      200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c y ^ 2 + σ * bondHullNorm c y) ∧
    ‖sqrtRemainder R c y‖ ≤
      200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c y ^ 2 + σ * bondHullNorm c y) := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set N := bondHullNorm c y with hN
  have hN0 : 0 ≤ N := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hσ0 : 0 ≤ σ := by
    have h0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro i
      have := hodd.pos
      simp only [Pi.zero_apply]
      omega
    exact (norm_nonneg _).trans (href 0 h0 1)
  have hN32 : N ≤ 1 / 32 := by nlinarith
  have hg := contoursNearReal_liftedField hodd hN32 href
  have hτ : 4 * (F.blockSide : ℝ) * (2 * N) ≤ 1 / 1024 := by linarith
  obtain ⟨h1, h2, h3⟩ := unitPart_and_sqrt_near hodd hj (by positivity : 0 ≤ 2 * N) hσ hτ hg
  refine ⟨h1, ?_, ?_⟩
  · set w : UnitQuaternion := polarUnit (contourAverage R c) with hw
    set gap : F.Site j → Fin 4 → ComplexQuat := linkDeviation (liftedField R y) R with hgap
    have hgapE : ∀ x i, gap x i = unitPart (1 + y x i) - 1 := fun x i => linkDeviation_liftedField R y x i
    set ε : F.Site j → Fin 4 → ComplexQuat := fun x i => gap x i - purePart (y x i) with hε
    have hdiff : purePart (transportedAverage R gap c) - purePart (transportedAverage R y c) =
        transportedAverage R (fun x i => purePart (ε x i)) c := by
      rw [purePart_transportedAverage, purePart_transportedAverage, ← transportedAverage_sub]
      congr 1
      funext x i
      simp only [hε, purePart_sub, purePart_purePart]
    have hlines : ∀ h ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide,
        ‖purePart (ε (lineBond c h r).1 (lineBond c h r).2)‖ ≤ 32 * N ^ 2 := by
      intro h hh r hr
      refine (norm_purePart_le _).trans ?_
      have hb := le_bondHullSum_of_line c (f := fun x i => ‖y x i‖) (fun _ _ => norm_nonneg _) hh hr
      have hb' : ‖y (lineBond c h r).1 (lineBond c h r).2‖ ≤ N := hb
      have := norm_unitPart_one_add_sub_le (e := y (lineBond c h r).1 (lineBond c h r).2) (by linarith)
      simp only [hε, hgapE]
      refine this.trans ?_
      gcongr
    have h4 : ‖transportedAverage R (fun x i => purePart (ε x i)) c‖ ≤ F.blockSide * (32 * N ^ 2) :=
      (norm_transportedAverage_le hodd R _ c).trans (lineBlockAverage_le hodd hlines)
    have h5 : unitRemainder R c y =
        (unitPart (liftedBondMean R c y) * ofUnit w⁻¹ - 1 - purePart (transportedAverage R gap c)) +
        (purePart (transportedAverage R gap c) - purePart (transportedAverage R y c)) := by
      rw [unitRemainder]
      abel
    rw [h5, hdiff]
    refine (norm_add_le _ _).trans ?_
    have h2' : ‖unitPart (liftedBondMean R c y) * ofUnit w⁻¹ - 1 - purePart (transportedAverage R gap c)‖ ≤
        700 * (4 * (F.blockSide : ℝ) * (2 * N)) ^ 2 + 20 * σ * (4 * (F.blockSide : ℝ) * (2 * N)) := h2
    have a1 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 2 * N ^ 2 := by positivity
    have a2 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 2 * (σ * N) := by positivity
    have a3 : (F.blockSide : ℝ) * N ^ 2 ≤ (F.blockSide : ℝ) ^ 2 * N ^ 2 := by
      have : (F.blockSide : ℝ) ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg N)
    have a4 : (F.blockSide : ℝ) * (σ * N) ≤ (F.blockSide : ℝ) ^ 2 * (σ * N) := by
      have : (F.blockSide : ℝ) ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    nlinarith
  · have h3' : ‖sqrtRemainder R c y‖ ≤
        1700 * (4 * (F.blockSide : ℝ) * (2 * N)) ^ 2 + 72 * σ * (4 * (F.blockSide : ℝ) * (2 * N)) := h3
    refine h3'.trans ?_
    have a1 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 2 * N ^ 2 := by positivity
    have a2 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 2 * (σ * N) := by positivity
    have a4 : (F.blockSide : ℝ) * (σ * N) ≤ (F.blockSide : ℝ) ^ 2 * (σ * N) := by
      have : (F.blockSide : ℝ) ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    nlinarith
end Remainders
section LineHolomorphy
def PathBondsSatisfy (Q : F.Site j → Fin 4 → Prop) : F.Site j → List PathStep → Prop
  | _, [] => True
  | x, st :: r => Q (crossedBond x st) st.1 ∧ PathBondsSatisfy Q (x + BlockAverages.stepDisplacement j st) r
theorem pathBondsSatisfy_of_allAlong {Q : F.Site j → Fin 4 → Prop} (x : F.Site j) {P : Lattice4 → Prop}
    (hb : ∀ v k, P v → P (v + basisVector k) → Q (x + siteOfCoords j v) k) {l : List PathStep} {v : Lattice4}
    (hp : AllAlong P v l) : PathBondsSatisfy Q (x + siteOfCoords j v) l := by
  induction l generalizing v with
  | nil => trivial
  | cons st r ih =>
    have hnext : P (v + FlatPairing.stepDisplacement st) := allAlong_head hp.2
    have hstep : x + siteOfCoords j v + BlockAverages.stepDisplacement j st =
        x + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rw [siteOfCoords_add, siteOfCoords_flatStep, add_assoc]
    refine ⟨?_, ?_⟩
    · rcases hs : st.2 with _ | _
      · have e1 : v + FlatPairing.stepDisplacement st = v - basisVector st.1 := by
          simp [FlatPairing.stepDisplacement, hs, sub_eq_add_neg]
        have e2 : crossedBond (x + siteOfCoords j v) st = x + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
          simp only [crossedBond, hs, Bool.false_eq_true, if_false]
          rw [e1, siteOfCoords_sub, unitStep_eq]
          abel
        rw [e2]
        exact hb (v + FlatPairing.stepDisplacement st) st.1 hnext (by
          rw [e1, sub_add_cancel]
          exact hp.1)
      · have e1 : v + FlatPairing.stepDisplacement st = v + basisVector st.1 := by
          simp [FlatPairing.stepDisplacement, hs]
        have e2 : crossedBond (x + siteOfCoords j v) st = x + siteOfCoords j v := by
          simp [crossedBond, hs]
        rw [e2]
        exact hb v st.1 hp.1 (e1 ▸ hnext)
    · rw [hstep]
      exact ih hp.2
theorem pathBondsSatisfy_axisPath {Q : F.Site j → Fin 4 → Prop} (x : F.Site j) (hL : 1 ≤ F.blockSide)
    (hb : ∀ v ∈ centredCube F.blockSide, ∀ k, v + Pi.single k 1 ∈ centredCube F.blockSide →
      Q (x + siteOfCoords j v) k)
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    PathBondsSatisfy Q x (axisPath h π) := by
  have h1 : AllAlong (fun v => v ∈ centredCube F.blockSide) 0 (axisPath h π) :=
    allAlong_mono (fun v hv => mem_centredCube_of_between hh hL hv) (axisPath_spec h π).1
  have h2 := pathBondsSatisfy_of_allAlong (Q := Q) x (P := fun v => v ∈ centredCube F.blockSide)
    (fun v k a b => hb v a k b) h1
  rwa [siteOfCoords_zero, add_zero] at h2
theorem pathBondsSatisfy_replicate {Q : F.Site j → Fin 4 → Prop} (x : F.Site j) (i : Fin 4) (m : ℕ)
    (hb : ∀ r ∈ Finset.range m, Q (x + (r : ℤ) • unitStep j i) i) :
    PathBondsSatisfy Q x (List.replicate m (i, true)) := by
  induction m generalizing x with
  | zero => trivial
  | succ m ih =>
    rw [List.replicate_succ]
    refine ⟨?_, ih _ fun r hr => ?_⟩
    · have := hb 0 (by simp)
      simpa [crossedBond] using this
    · have := hb (r + 1) (by simpa using hr)
      have e : x + BlockAverages.stepDisplacement j (i, true) + (r : ℤ) • unitStep j i =
          x + ((r + 1 : ℕ) : ℤ) • unitStep j i := by
        simp only [BlockAverages.stepDisplacement, if_true]
        push_cast
        rw [add_smul, one_smul]
        abel
      rw [e]
      exact this
theorem differentiableAt_complexPathHolonomy {X : ℂ → F.ComplexField j} {z : ℂ} {x : F.Site j}
    {l : List PathStep} (h : PathBondsSatisfy (fun b i => DifferentiableAt ℂ (fun w => X w b i) z) x l) :
    DifferentiableAt ℂ (fun w => complexPathHolonomy (X w) x l) z := by
  induction l generalizing x with
  | nil => simp only [complexPathHolonomy]; exact differentiableAt_const _
  | cons st r ih =>
    simp only [complexPathHolonomy]
    refine DifferentiableAt.fun_mul ?_ (ih h.2)
    rcases hs : st.2 with _ | _
    · have h1 := h.1
      simp only [crossedBond, hs, Bool.false_eq_true, if_false] at h1
      simp only [complexLinkValue, hs, Bool.false_eq_true, if_false]
      exact differentiableAt_adjugate_comp h1
    · have h1 := h.1
      simp only [crossedBond, hs, if_true] at h1
      simp only [complexLinkValue, hs, if_true]
      exact h1
theorem one_add_ne_zero_and_det_mem_slitPlane {e : ComplexQuat} (he : ‖e‖ ≤ 1 / 8) :
    ((1 : ComplexQuat) + e) ≠ 0 ∧ ((1 : ComplexQuat) + e).det ∈ Complex.slitPlane := by
  refine ⟨one_add_ne_zero_of_norm_lt_one (by linarith), ?_⟩
  rw [det_one_add]
  have h1 := norm_trace_le e
  have h2 := norm_det_le e
  have h3 := norm_add_le e.trace e.det
  have h4 := norm_nonneg e
  have h5 : ‖e.trace + e.det‖ ≤ 1 / 2 := by nlinarith
  have h6 := (abs_le.1 ((Complex.abs_re_le_norm _).trans h5)).1
  left
  simp only [Complex.add_re, Complex.one_re]
  simp only [Complex.add_re] at h6
  linarith
theorem differentiableAt_fieldLine (y e : F.Site j → Fin 4 → ComplexQuat) (z : ℂ) (b : F.Site j) (i : Fin 4) :
    DifferentiableAt ℂ (fun w => (y + w • e) b i) z := by
  have : (fun w : ℂ => (y + w • e) b i) = fun w => y b i + w • e b i := rfl
  rw [this]
  exact (differentiableAt_const _).fun_add (differentiableAt_id.fun_smul (differentiableAt_const _))
theorem differentiableAt_liftedField (R : F.GaugeField j) (y e : F.Site j → Fin 4 → ComplexQuat) {z : ℂ}
    {b : F.Site j} {i : Fin 4} (hb : ‖(y + z • e) b i‖ ≤ 1 / 8) :
    DifferentiableAt ℂ (fun w => liftedField R (y + w • e) b i) z := by
  obtain ⟨h1, h2⟩ := one_add_ne_zero_and_det_mem_slitPlane hb
  simp only [liftedField]
  refine DifferentiableAt.fun_mul ?_ (differentiableAt_const _)
  exact differentiableAt_unitPart_comp
    ((differentiableAt_const _).fun_add (differentiableAt_fieldLine y e z b i)) h1 h2
theorem norm_complexRelativePathAverage_sub_one_le (hodd : Odd F.blockSide) {X : F.ComplexField j}
    {R : F.GaugeField j} {t : ℝ} (ht : 0 ≤ t) (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1) {y0 : F.Site (j + 1)}
    (hp : ∀ h ∈ centredCube F.blockSide, ∀ π, PathNearReal X R t (refineSite y0) (axisPath h π)) :
    ‖complexRelativePathAverage X R y0 - 1‖ ≤ 4 * (F.blockSide : ℝ) * t := by
  have h1 : complexRelativePathAverage X R y0 - 1 =
      blockContourMean F (fun h π => relativeHolonomy X R (refineSite y0) (axisPath h π) - 1) := by
    rw [blockContourMean_sub, blockContourMean_const hodd]
    rfl
  rw [h1]
  refine norm_blockContourMean_le hodd fun h hh π => ?_
  have := norm_relativeHolonomy_sub_one_le_of_length_le ht (hp h hh π) (length_axisPath_le F.blockSide h hh π)
    (by push_cast; linarith)
  refine this.trans (le_of_eq ?_)
  push_cast
  ring
theorem differentiableAt_liftedBondMean (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    (y e : F.Site j → Fin 4 → ComplexQuat) {c : F.Site (j + 1) × Fin 4} {σ z : ℝ} {zc : ℂ}
    (hy : 8 * (F.blockSide : ℝ) * bondHullNorm c (y + zc • e) ≤ 1 / 1024)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ) :
    DifferentiableAt ℂ (fun w => liftedBondMean R c (y + w • e)) zc := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  set N := bondHullNorm c (y + zc • e) with hN
  have hN0 : 0 ≤ N := bondHullSum_nonneg c fun _ _ => norm_nonneg _
  have hN32 : N ≤ 1 / 32 := by nlinarith
  have hnn : ∀ x i, (0 : ℝ) ≤ ‖(y + zc • e) x i‖ := fun _ _ => norm_nonneg _
  have hg := contoursNearReal_liftedField hodd hN32 href
  have hb : ∀ {b i}, ‖(y + zc • e) b i‖ ≤ N →
      DifferentiableAt ℂ (fun w => liftedField R (y + w • e) b i) zc :=
    fun h => differentiableAt_liftedField R y e (h.trans (by linarith))
  set X : ℂ → F.ComplexField j := fun w => liftedField R (y + w • e) with hX
  have hleg : ∀ h ∈ centredCube F.blockSide, ∀ π,
      DifferentiableAt ℂ (fun w => complexPathHolonomy (X w) (refineSite c.1) (axisPath h π)) zc :=
    fun h hh π =>
    differentiableAt_complexPathHolonomy (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk =>
      hb (le_bondHullSum_of_block c hnn hv k hk).1) hh π)
  have hleg' : ∀ h ∈ centredCube F.blockSide, ∀ π, DifferentiableAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π)) zc :=
    fun h hh π =>
    differentiableAt_complexPathHolonomy (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk =>
      hb (le_bondHullSum_of_block c hnn hv k hk).2) hh π)
  have hline : ∀ h ∈ centredCube F.blockSide, DifferentiableAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite c.1 + siteOfCoords j h)
        (List.replicate F.blockSide (c.2, true))) zc := fun h hh =>
    differentiableAt_complexPathHolonomy
      (pathBondsSatisfy_replicate _ _ _ fun r hr => hb (le_bondHullSum_of_line c hnn hh hr))
  have hcm : DifferentiableAt ℂ (fun w => complexContourAverage (X w) c) zc := by
    simp only [complexContourAverage]
    have hs : DifferentiableAt ℂ (fun w => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        complexPathHolonomy (X w) (refineSite c.1) (bondContour F.blockSide h π c.2)) zc := by
      refine DifferentiableAt.fun_sum fun h hh => DifferentiableAt.fun_sum fun π _ => ?_
      simp only [complexPathHolonomy_bondContour hj]
      exact ((hleg h hh π).fun_mul (hline h hh)).fun_mul (differentiableAt_adjugate_comp (hleg' h hh π))
    exact hs.const_smul (contourWeight F)
  have hlink : ∀ y0 : F.Site (j + 1),
      (∀ h ∈ centredCube F.blockSide, ∀ π,
        DifferentiableAt ℂ (fun w => complexPathHolonomy (X w) (refineSite y0) (axisPath h π)) zc) →
      (∀ h ∈ centredCube F.blockSide, ∀ π, PathNearReal (X zc) R (2 * N) (refineSite y0) (axisPath h π)) →
      DifferentiableAt ℂ (fun w => complexBalancingGauge (X w) R y0) zc := by
    intro y0 hd hp
    have h1 := norm_complexRelativePathAverage_sub_one_le hodd (by positivity : 0 ≤ 2 * N) (by linarith) hp
    have h2 : ‖complexRelativePathAverage (X zc) R y0 - 1‖ ≤ 1 / 8 := by linarith
    obtain ⟨h3, h4⟩ := one_add_ne_zero_and_det_mem_slitPlane h2
    rw [add_sub_cancel] at h3 h4
    simp only [complexBalancingGauge]
    refine differentiableAt_adjugate_comp (differentiableAt_unitPart_comp ?_ h3 h4)
    simp only [complexRelativePathAverage]
    have hs : DifferentiableAt ℂ (fun w => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        complexPathHolonomy (X w) (refineSite y0) (axisPath h π) *
          ofUnit (pathHolonomy R (refineSite y0) (axisPath h π))⁻¹) zc := by
      refine DifferentiableAt.fun_sum fun h hh => DifferentiableAt.fun_sum fun π _ => ?_
      exact (hd h hh π).fun_mul (differentiableAt_const _)
    exact hs.const_smul (contourWeight F)
  have hk := hlink c.1 hleg hg.nearLegs
  have hk' := hlink (c.1 + unitStep (j + 1) c.2) hleg' hg.nearFarLegs
  simp only [liftedBondMean, complexGaugedContourAverage]
  exact (hk.fun_mul hcm).fun_mul (differentiableAt_adjugate_comp hk')
end LineHolomorphy
end ComplexRemainders
end YangMills.Construction
end
