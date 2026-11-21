import YangMills.Construction.SummableBoundsOfTheFlow.TheTailOfTheGapIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HaarGapTailRegularity
section
open Set Filter Topology MeasureTheory
open scoped Interval
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
theorem continuousOn_slice {H : Type} [TopologicalSpace H] {I : Set ℝ} {U : Set E}
    (hIc : Icc (0 : ℝ) 1 ⊆ I) {Φ : ℝ × E → H} {x : E} (hx : x ∈ U)
    (hΦ : ContinuousOn Φ (I ×ˢ U)) : ContinuousOn (fun v => Φ (v, x)) (Icc (0 : ℝ) 1) :=
  hΦ.comp (by fun_prop) fun _ hv => ⟨hIc hv, hx⟩
theorem aestronglyMeasurable_slice {H : Type} [NormedAddCommGroup H] {I : Set ℝ} {U : Set E}
    (hIc : Icc (0 : ℝ) 1 ⊆ I) {Φ : ℝ × E → H} {x : E} (hx : x ∈ U)
    (hΦ : ContinuousOn Φ (I ×ˢ U)) :
    AEStronglyMeasurable (fun v => Φ (v, x)) (volume.restrict (Ι (0 : ℝ) 1)) := by
  refine ContinuousOn.aestronglyMeasurable ((continuousOn_slice hIc hx hΦ).mono ?_) measurableSet_uIoc
  rw [uIoc_of_le zero_le_one]
  exact Ioc_subset_Icc_self
theorem exists_closedBall_bound {H : Type} [NormedAddCommGroup H] {I : Set ℝ} {U : Set E}
    (hIc : Icc (0 : ℝ) 1 ⊆ I) (hU : IsOpen U) {Φ : ℝ × E → H} {x : E} (hx : x ∈ U)
    (hΦ : ContinuousOn Φ (I ×ˢ U)) :
    ∃ r C : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ U ∧
      ∀ v ∈ Icc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall x r, ‖Φ (v, y)‖ ≤ C := by
  haveI := FiniteDimensional.proper_real E
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x r) :=
    isCompact_Icc.prod (isCompact_closedBall x r)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hΦ.mono (Set.prod_mono hIc hrU))
  exact ⟨r, C, hr, hrU, fun v hv y hy => hC (v, y) ⟨hv, hy⟩⟩
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
theorem continuousOn_intervalIntegral_param {I : Set ℝ} {U : Set E} (hI : IsOpen I)
    (hIc : Icc (0 : ℝ) 1 ⊆ I) (hU : IsOpen U) {Φ : ℝ × E → H} (hΦ : ContinuousOn Φ (I ×ˢ U)) :
    ContinuousOn (fun x => ∫ v in (0 : ℝ)..1, Φ (v, x)) U := by
  intro x₀ hx₀
  obtain ⟨r, C, hr, hrU, hC⟩ := exists_closedBall_bound hIc hU hx₀ hΦ
  have hb : Metric.closedBall x₀ r ∈ 𝓝 x₀ := Metric.closedBall_mem_nhds x₀ hr
  apply ContinuousAt.continuousWithinAt
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hb] with x hx
    exact aestronglyMeasurable_slice hIc (hrU hx) hΦ
  · filter_upwards [hb] with x hx
    refine Eventually.of_forall fun t ht => hC t ?_ x hx
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have h1 : ContinuousAt Φ (t, x₀) :=
      hΦ.continuousAt ((hI.prod hU).mem_nhds ⟨hIc (Ioc_subset_Icc_self ht), hx₀⟩)
    exact ContinuousAt.comp (f := fun x => (t, x)) h1 (by fun_prop)
def partialFDerivSnd (Φ : ℝ × E → H) (p : ℝ × E) : E →L[ℝ] H :=
  (fderiv ℝ Φ p).comp (ContinuousLinearMap.inr ℝ ℝ E)
theorem continuousOn_partialFDerivSnd {I : Set ℝ} {U : Set E} (hI : IsOpen I) (hU : IsOpen U)
    {Φ : ℝ × E → H} (hΦ : ContDiffOn ℝ 1 Φ (I ×ˢ U)) :
    ContinuousOn (partialFDerivSnd Φ) (I ×ˢ U) :=
  (hΦ.continuousOn_fderiv_of_isOpen (hI.prod hU) le_rfl).clm_comp continuousOn_const
theorem hasFDerivAt_intervalIntegral_param {M : ℝ → ℝ} (hM : Continuous M) {I : Set ℝ} {U : Set E}
    (hI : IsOpen I) (hIc : Icc (0 : ℝ) 1 ⊆ I) (hU : IsOpen U) {Φ : ℝ × E → H}
    (hΦ : ContDiffOn ℝ 1 Φ (I ×ˢ U)) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x))
      (∫ v in (0 : ℝ)..1, M v • partialFDerivSnd Φ (v, x)) x := by
  have hc : ContinuousOn (fun p : ℝ × E => M p.1 • partialFDerivSnd Φ p) (I ×ˢ U) :=
    (hM.comp continuous_fst).continuousOn.smul (continuousOn_partialFDerivSnd hI hU hΦ)
  have hΦc : ContinuousOn (fun p : ℝ × E => M p.1 • Φ p) (I ×ˢ U) :=
    (hM.comp continuous_fst).continuousOn.smul hΦ.continuousOn
  obtain ⟨r, C, hr, hrU, hC⟩ :=
    exists_closedBall_bound (Φ := fun p : ℝ × E => M p.1 • partialFDerivSnd Φ p) hIc hU hx hc
  have hb : Metric.closedBall x r ∈ 𝓝 x := Metric.closedBall_mem_nhds x hr
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => M t • Φ (t, x)) (F' := fun x t => M t • partialFDerivSnd Φ (t, x))
    (bound := fun _ => C)
    hb ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hb] with y hy
    exact aestronglyMeasurable_slice (Φ := fun p : ℝ × E => M p.1 • Φ p) hIc (hrU hy) hΦc
  · exact ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le zero_le_one]
      exact continuousOn_slice (Φ := fun p : ℝ × E => M p.1 • Φ p) hIc hx hΦc)
  · exact aestronglyMeasurable_slice (Φ := fun p : ℝ × E => M p.1 • partialFDerivSnd Φ p) hIc hx hc
  · refine Eventually.of_forall fun t ht y hy => hC t ?_ y hy
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · refine Eventually.of_forall fun t ht y hy => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hp : (t, y) ∈ I ×ˢ U := ⟨hIc (Ioc_subset_Icc_self ht), hrU hy⟩
    have hd : DifferentiableAt ℝ Φ (t, y) :=
      ((hΦ (t, y) hp).contDiffAt ((hI.prod hU).mem_nhds hp)).differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).const_smul (M t)
end
theorem contDiffOn_intervalIntegral_param {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] {M : ℝ → ℝ},
      Continuous M → ∀ {I : Set ℝ} {U : Set E}, IsOpen I → Icc (0 : ℝ) 1 ⊆ I → IsOpen U →
      ∀ {Φ : ℝ × E → H}, ContDiffOn ℝ n Φ (I ×ˢ U) →
        ContDiffOn ℝ n (fun x => ∫ v in (0 : ℝ)..1, M v • Φ (v, x)) U := by
  intro n
  induction n with
  | zero =>
    intro H _ _ _ M hM I U hI hIc hU Φ hΦ
    simp only [Nat.cast_zero, contDiffOn_zero] at hΦ ⊢
    exact continuousOn_intervalIntegral_param (Φ := fun p : ℝ × E => M p.1 • Φ p) hI hIc hU
      ((hM.comp continuous_fst).continuousOn.smul hΦ)
  | succ n ih =>
    intro H _ _ _ M hM I U hI hIc hU Φ hΦ
    have hΦ1 : ContDiffOn ℝ 1 Φ (I ×ˢ U) := hΦ.of_le (by norm_cast; omega)
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx =>
      (hasFDerivAt_intervalIntegral_param hM hI hIc hU hΦ1 hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have h1 : ContDiffOn ℝ n (partialFDerivSnd Φ) (I ×ˢ U) := by
      rw [hcast] at hΦ
      have := ((contDiffOn_succ_iff_fderiv_of_isOpen (hI.prod hU)).1 hΦ).2.2
      exact this.clm_comp contDiffOn_const
    refine (ih _ hM hI hIc hU h1).congr fun x hx => ?_
    exact (hasFDerivAt_intervalIntegral_param hM hI hIc hU hΦ1 hx).fderiv
end
section
open Set Filter Topology MeasureTheory
open scoped Interval
def flatWeight (p y : ℝ) : ℝ := if 0 < y then y ^ (-p) * Real.exp (-y⁻¹) else 0
theorem flatWeight_of_nonpos (p : ℝ) {y : ℝ} (hy : y ≤ 0) : flatWeight p y = 0 := by
  simp [flatWeight, not_lt.2 hy]
theorem flatWeight_of_pos (p : ℝ) {y : ℝ} (hy : 0 < y) :
    flatWeight p y = y ^ (-p) * Real.exp (-y⁻¹) := by
  simp [flatWeight, hy]
theorem exists_abs_flatWeight_le_sq {p : ℝ} (hp : 0 ≤ p) :
    ∃ C : ℝ, ∀ y : ℝ, |y| ≤ 1 → |flatWeight p y| ≤ C * |y ^ 2| := by
  set N : ℕ := ⌈p⌉₊ + 2 with hN
  refine ⟨N.factorial, fun y hy => ?_⟩
  by_cases h0 : 0 < y
  · rw [flatWeight_of_pos p h0, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hy1 : y ≤ 1 := (le_abs_self y).trans hy
    have h1 := Real.pow_div_factorial_le_exp y⁻¹ (by positivity) N
    have h2 : Real.exp (-y⁻¹) ≤ N.factorial * y ^ N := by
      rw [Real.exp_neg]
      have hf : (0 : ℝ) < N.factorial := by positivity
      have h3 : (N.factorial * y ^ N)⁻¹ ≤ Real.exp y⁻¹ := by
        refine le_trans (le_of_eq ?_) h1
        rw [inv_pow, mul_inv]
        field_simp
      have h4 := inv_anti₀ (by positivity) h3
      rwa [inv_inv] at h4
    have h5 : y ^ (-p) * (y ^ N : ℝ) ≤ y ^ 2 := by
      have e1 : y ^ (-p) * (y ^ N : ℝ) = y ^ (-p + N) := by
        rw [Real.rpow_add h0, Real.rpow_natCast]
      have e2 : (y ^ 2 : ℝ) = y ^ (2 : ℝ) := by norm_cast
      rw [e1, e2]
      refine Real.rpow_le_rpow_of_exponent_ge h0 hy1 ?_
      have : p ≤ ⌈p⌉₊ := Nat.le_ceil p
      simp only [hN]
      push_cast
      linarith
    calc y ^ (-p) * Real.exp (-y⁻¹) ≤ y ^ (-p) * (N.factorial * y ^ N) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = N.factorial * (y ^ (-p) * (y ^ N : ℝ)) := by ring
      _ ≤ N.factorial * y ^ 2 := mul_le_mul_of_nonneg_left h5 (by positivity)
  · rw [flatWeight_of_nonpos p (not_lt.1 h0)]
    simp only [abs_zero]
    positivity
theorem flatWeight_hasDerivAt {p : ℝ} (hp : 0 ≤ p) (y : ℝ) :
    HasDerivAt (flatWeight p) (-p * flatWeight (p + 1) y + flatWeight (p + 2) y) y := by
  rcases lt_trichotomy y 0 with h | h | h
  · rw [flatWeight_of_nonpos _ h.le, flatWeight_of_nonpos _ h.le]
    have : flatWeight p =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with z hz
      exact flatWeight_of_nonpos p (le_of_lt hz)
    simpa using (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq this
  · subst h
    rw [flatWeight_of_nonpos _ le_rfl, flatWeight_of_nonpos _ le_rfl]
    obtain ⟨C, hC⟩ := exists_abs_flatWeight_le_sq hp
    simp only [mul_zero, add_zero]
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have h1 : (fun h : ℝ => flatWeight p (0 + h) - flatWeight p 0 - h • (0 : ℝ)) =O[𝓝 0]
        fun h : ℝ => h ^ 2 := by
      refine Asymptotics.IsBigO.of_bound C ?_
      have : ∀ᶠ h : ℝ in 𝓝 0, |h| ≤ 1 := by
        have := Metric.ball_mem_nhds (0 : ℝ) one_pos
        filter_upwards [this] with h hh
        simpa using (Metric.mem_ball.1 hh).le
      filter_upwards [this] with h hh
      simpa [flatWeight_of_nonpos p (le_refl (0 : ℝ))] using hC h hh
    exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))
  · rw [flatWeight_of_pos _ h, flatWeight_of_pos _ h]
    have hev : flatWeight p =ᶠ[𝓝 y] fun z => z ^ (-p) * Real.exp (-z⁻¹) := by
      filter_upwards [Ioi_mem_nhds h] with z hz
      exact flatWeight_of_pos p hz
    have h1 : HasDerivAt (fun z : ℝ => z ^ (-p)) (-p * y ^ (-p - 1)) y :=
      Real.hasDerivAt_rpow_const (Or.inl h.ne')
    have h2 : HasDerivAt (fun z : ℝ => Real.exp (-z⁻¹)) (Real.exp (-y⁻¹) * (y ^ 2)⁻¹) y := by
      have := ((hasDerivAt_inv h.ne').neg).exp
      simpa using this
    refine (h1.mul h2).congr_of_eventuallyEq hev |>.congr_deriv ?_
    have e1 : y ^ (-(p + 1)) = y ^ (-p - 1) := by congr 1; ring
    have e2 : y ^ (-(p + 2)) = y ^ (-p) * (y ^ 2)⁻¹ := by
      have : -(p + 2) = -p + (-2 : ℝ) := by ring
      rw [this, Real.rpow_add h, Real.rpow_neg h.le]
      norm_cast
    rw [e1, e2]
    ring
theorem flatWeight_contDiff : ∀ (n : ℕ) (p : ℝ), 0 ≤ p → ContDiff ℝ n (flatWeight p) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    simp only [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun y => (flatWeight_hasDerivAt hp y).continuousAt
  | succ n ih =>
    intro p hp
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiff_succ_iff_deriv]
    refine ⟨fun y => (flatWeight_hasDerivAt hp y).differentiableAt, by simp, ?_⟩
    have : deriv (flatWeight p) = fun y => -p * flatWeight (p + 1) y + flatWeight (p + 2) y :=
      funext fun y => (flatWeight_hasDerivAt hp y).deriv
    rw [this]
    exact (contDiff_const.mul (ih (p + 1) (by linarith))).add (ih (p + 2) (by linarith))
def weightedLaplace (a : ℝ) (θ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), Real.exp (-v) * v ^ a * θ (u * v)
theorem integrableOn_exp_neg_mul_rpow {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun v : ℝ => Real.exp (-v) * v ^ a) (Ioi 0) := by
  have := Real.GammaIntegral_convergent (s := a + 1) (by linarith)
  simpa using this
theorem weightedLaplace_integrableOn {a : ℝ} (ha : -1 < a) {θ : ℝ → ℝ} (hθ : Continuous θ)
    {C : ℝ} (hC : ∀ x, |θ x| ≤ C) (u : ℝ) :
    IntegrableOn (fun v : ℝ => Real.exp (-v) * v ^ a * θ (u * v)) (Ioi 0) := by
  refine Integrable.mul_bdd (c := C) (integrableOn_exp_neg_mul_rpow ha) ?_ ?_
  · exact (hθ.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun v => by simpa using hC _
theorem weightedLaplace_hasDerivAt {a : ℝ} (ha : -1 < a) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    (hc : HasCompactSupport θ) (hc' : HasCompactSupport (deriv θ)) (u : ℝ) :
    HasDerivAt (weightedLaplace a θ) (weightedLaplace (a + 1) (deriv θ) u) u := by
  have hθc : Continuous θ := hθ.continuous
  have hdc : Continuous (deriv θ) := hθ.continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hθc
  obtain ⟨C', hC'⟩ := hc'.exists_bound_of_continuous hdc
  have hC1 : ∀ x, |θ x| ≤ C := fun x => by simpa using hC x
  have hC1' : ∀ x, |deriv θ x| ≤ C' := fun x => by simpa using hC' x
  have hint := weightedLaplace_integrableOn (a := a + 1) (by linarith) hdc hC1' u
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun u v => Real.exp (-v) * v ^ a * θ (u * v))
    (F' := fun u v => Real.exp (-v) * v ^ (a + 1) * deriv θ (u * v))
    (bound := fun v => Real.exp (-v) * v ^ (a + 1) * C') (x₀ := u) (s := univ) univ_mem
    (Eventually.of_forall fun u' => (weightedLaplace_integrableOn ha hθc hC1 u').aestronglyMeasurable)
    (weightedLaplace_integrableOn ha hθc hC1 u) hint.aestronglyMeasurable ?_
    ((integrableOn_exp_neg_mul_rpow (a := a + 1) (by linarith)).mul_const C') ?_
  · exact hmain.2
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv x _ => ?_)
    have hv' : (0 : ℝ) < v := hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-v) * v ^ (a + 1))]
    exact mul_le_mul_of_nonneg_left (hC1' _) (by positivity)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv x _ => ?_)
    have hv' : (0 : ℝ) < v := hv
    have hd : HasDerivAt θ (deriv θ (x * v)) (x * v) :=
      (hθ.differentiable (by norm_num) _).hasDerivAt
    have h1 : HasDerivAt (fun u' : ℝ => u' * v) v x := by
      simpa using (hasDerivAt_id x).mul_const v
    have h2 := (hd.comp x h1).const_mul (Real.exp (-v) * v ^ a)
    refine h2.congr_deriv ?_
    rw [Real.rpow_add hv', Real.rpow_one]
    ring
theorem weightedLaplace_contDiff : ∀ (n : ℕ) (a : ℝ) (θ : ℝ → ℝ), -1 < a →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ → HasCompactSupport θ →
      ContDiff ℝ n (weightedLaplace a θ) := by
  intro n
  have hderiv : ∀ θ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv θ) := fun θ h => (contDiff_infty_iff_deriv.1 h).2
  have h1 : ∀ θ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ → ContDiff ℝ 1 θ :=
    fun θ h => h.of_le (by exact_mod_cast le_top)
  induction n with
  | zero =>
    intro a θ ha hθ hc
    simp only [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun u =>
      (weightedLaplace_hasDerivAt ha (h1 θ hθ) hc hc.deriv u).continuousAt
  | succ n ih =>
    intro a θ ha hθ hc
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiff_succ_iff_deriv]
    refine ⟨fun u => (weightedLaplace_hasDerivAt ha (h1 θ hθ) hc hc.deriv u).differentiableAt,
      by simp, ?_⟩
    have : deriv (weightedLaplace a θ) = weightedLaplace (a + 1) (deriv θ) :=
      funext fun u => (weightedLaplace_hasDerivAt ha (h1 θ hθ) hc hc.deriv u).deriv
    rw [this]
    exact ih (a + 1) (deriv θ) (by linarith) (hderiv θ hθ) hc.deriv
def sqrtCutoff (w : ℝ) : ℝ := Real.smoothTransition (3 - 2 * w) * Real.smoothTransition (w + 2)
def cutoffSqrt (w : ℝ) : ℝ := sqrtCutoff w * Real.sqrt (2 - w)
theorem sqrtCutoff_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sqrtCutoff :=
  (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))
theorem sqrtCutoff_eq_one {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : sqrtCutoff w = 1 := by
  simp only [sqrtCutoff]
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  simp
theorem sqrtCutoff_eq_zero_of_ge {w : ℝ} (h : 3 / 2 ≤ w) : sqrtCutoff w = 0 := by
  simp only [sqrtCutoff]
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp
theorem sqrtCutoff_eq_zero_of_le {w : ℝ} (h : w ≤ -2) : sqrtCutoff w = 0 := by
  simp only [sqrtCutoff]
  rw [Real.smoothTransition.zero_of_nonpos (x := w + 2) (by linarith)]
  simp
theorem cutoffSqrt_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cutoffSqrt := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases h : w < 2
  · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => Real.sqrt (2 - w)) w :=
      ContDiffAt.sqrt (by fun_prop) (by linarith : (0 : ℝ) < 2 - w).ne'
    exact sqrtCutoff_contDiff.contDiffAt.mul h1
  · have h1 : cutoffSqrt =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds (by linarith : (3 / 2 : ℝ) < w)] with z hz
      simp [cutoffSqrt, sqrtCutoff_eq_zero_of_ge (le_of_lt hz)]
    exact contDiffAt_const.congr_of_eventuallyEq h1
theorem cutoffSqrt_hasCompactSupport : HasCompactSupport cutoffSqrt := by
  refine HasCompactSupport.intro (K := Icc (-2 : ℝ) (3 / 2)) isCompact_Icc fun w hw => ?_
  simp only [mem_Icc, not_and_or, not_le] at hw
  rcases hw with h | h
  · simp [cutoffSqrt, sqrtCutoff_eq_zero_of_le h.le]
  · simp [cutoffSqrt, sqrtCutoff_eq_zero_of_ge h.le]
def clampedSqrt (w : ℝ) : ℝ := Real.sqrt (2 - max w 0)
def sqrtRemainder (w : ℝ) : ℝ := clampedSqrt w - cutoffSqrt w
theorem clampedSqrt_continuous : Continuous clampedSqrt := by
  unfold clampedSqrt
  fun_prop
theorem sqrtRemainder_continuous : Continuous sqrtRemainder :=
  clampedSqrt_continuous.sub cutoffSqrt_contDiff.continuous
theorem abs_clampedSqrt_le (w : ℝ) : |clampedSqrt w| ≤ Real.sqrt 2 := by
  simp only [clampedSqrt]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (by have := le_max_right w 0; linarith)
theorem exists_abs_sqrtRemainder_le : ∃ C : ℝ, ∀ w, |sqrtRemainder w| ≤ C := by
  obtain ⟨C, hC⟩ :=
    cutoffSqrt_hasCompactSupport.exists_bound_of_continuous cutoffSqrt_contDiff.continuous
  refine ⟨Real.sqrt 2 + C, fun w => ?_⟩
  have := hC w
  rw [Real.norm_eq_abs] at this
  exact (abs_sub _ _).trans (add_le_add (abs_clampedSqrt_le w) this)
theorem sqrtRemainder_eq_zero_of_le_one {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : sqrtRemainder w = 0 := by
  simp [sqrtRemainder, clampedSqrt, cutoffSqrt, sqrtCutoff_eq_one h0 h1, max_eq_left h0]
theorem sqrtRemainder_eq_zero_of_two_le {w : ℝ} (h : 2 ≤ w) : sqrtRemainder w = 0 := by
  have hs : Real.sqrt (2 - w) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
  have h0 : 0 ≤ w := by linarith
  simp [sqrtRemainder, clampedSqrt, cutoffSqrt, max_eq_left h0, hs]
def remainderIntegral (u : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, (sqrtRemainder (1 + v) / (1 + |v|)) • flatWeight (3 / 2) (u / (1 + v))
theorem remainderIntegral_contDiff (n : ℕ) : ContDiff ℝ n remainderIntegral := by
  have hM : Continuous fun v : ℝ => sqrtRemainder (1 + v) / (1 + |v|) :=
    (sqrtRemainder_continuous.comp (by fun_prop)).div (by fun_prop)
      fun v => by positivity
  have hΦ : ContDiffOn ℝ n (fun p : ℝ × ℝ => flatWeight (3 / 2) (p.2 / (1 + p.1)))
      (Ioi (-(1 / 2) : ℝ) ×ˢ (univ : Set ℝ)) := by
    refine (flatWeight_contDiff n (3 / 2) (by norm_num)).comp_contDiffOn ?_
    refine ContDiffOn.div contDiffOn_snd (by fun_prop) ?_
    intro p hp
    have h1 : -(1 / 2) < p.1 := hp.1
    intro h0
    linarith
  have h := contDiffOn_intervalIntegral_param n ℝ hM isOpen_Ioi (fun v hv => by
    have : (0 : ℝ) ≤ v := hv.1
    simp only [mem_Ioi]
    linarith) isOpen_univ hΦ
  exact contDiffOn_univ.1 h
theorem weightedLaplace_sqrtRemainder_eq {u : ℝ} (hu : 0 ≤ u) :
    weightedLaplace (1 / 2) sqrtRemainder u = remainderIntegral u := by
  rcases hu.eq_or_lt with rfl | hu
  · have h0 : sqrtRemainder 0 = 0 := sqrtRemainder_eq_zero_of_le_one le_rfl zero_le_one
    simp [weightedLaplace, remainderIntegral, h0, flatWeight_of_nonpos]
  · set g : ℝ → ℝ := fun w => Real.exp (-(w / u)) * (w / u) ^ (1 / 2 : ℝ) * sqrtRemainder w with hg
    have h1 : weightedLaplace (1 / 2) sqrtRemainder u = ∫ v in Ioi (0 : ℝ), g (u * v) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      simp only [hg]
      rw [mul_div_cancel_left₀ v hu.ne']
    have h3 : ∫ x in Ioi (0 : ℝ), g x = ∫ x in Ioc (1 : ℝ) 2, g x := by
      refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
        (fun x hx => lt_trans one_pos hx.1) fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      have hr : sqrtRemainder x = 0 := by
        by_cases h1 : x ≤ 1
        · exact sqrtRemainder_eq_zero_of_le_one hx0.le h1
        · refine sqrtRemainder_eq_zero_of_two_le ?_
          by_contra h2
          exact hx.2 ⟨not_le.1 h1, (not_le.1 h2).le⟩
      simp [hg, hr]
    have h5 : ∫ x in (1 : ℝ)..2, g x = ∫ v in (0 : ℝ)..1, g (1 + v) := by
      have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := 1) g 1
      have e1 : (1 : ℝ) + 0 = 1 := by norm_num
      have e2 : (1 : ℝ) + 1 = 2 := by norm_num
      rw [e1, e2] at h
      exact h.symm
    have h6 : remainderIntegral u = ∫ v in (0 : ℝ)..1, u⁻¹ * g (1 + v) := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le zero_le_one] at hv
      have hv0 : (0 : ℝ) ≤ v := hv.1
      have hy : (0 : ℝ) < (1 + v) / u := by positivity
      have hy' : (0 : ℝ) < u / (1 + v) := by positivity
      simp only [abs_of_nonneg hv0, smul_eq_mul, hg]
      rw [flatWeight_of_pos _ hy']
      have e1 : (u / (1 + v))⁻¹ = (1 + v) / u := inv_div _ _
      have e2 : (u / (1 + v)) ^ (-(3 / 2 : ℝ)) = ((1 + v) / u) * ((1 + v) / u) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_neg hy'.le, ← Real.inv_rpow hy'.le, e1]
        have : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
        rw [this, Real.rpow_add hy, Real.rpow_one]
      rw [e1, e2]
      field_simp
    rw [h1, integral_comp_mul_left_Ioi g 0 hu, mul_zero, h3,
      ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2), h5, h6,
      intervalIntegral.integral_const_mul, smul_eq_mul]
theorem weightedLaplace_clampedSqrt_eq {u : ℝ} (hu : 0 ≤ u) :
    weightedLaplace (1 / 2) clampedSqrt u =
      weightedLaplace (1 / 2) cutoffSqrt u + remainderIntegral u := by
  rw [← weightedLaplace_sqrtRemainder_eq hu]
  obtain ⟨C, hC⟩ :=
    cutoffSqrt_hasCompactSupport.exists_bound_of_continuous cutoffSqrt_contDiff.continuous
  obtain ⟨C', hC'⟩ := exists_abs_sqrtRemainder_le
  have i1 := weightedLaplace_integrableOn (a := 1 / 2) (by norm_num) cutoffSqrt_contDiff.continuous
    (fun x => by simpa using hC x) u
  have i2 := weightedLaplace_integrableOn (a := 1 / 2) (by norm_num) sqrtRemainder_continuous hC' u
  simp only [weightedLaplace]
  rw [← integral_add i1 i2]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [sqrtRemainder]
  ring
theorem integral_sqrt_eq_weightedLaplace {u : ℝ} (hu : 0 ≤ u) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * Real.sqrt v * Real.sqrt (2 - u * v) =
      weightedLaplace (1 / 2) clampedSqrt u := by
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0 : ℝ) < v := hv
  simp only [clampedSqrt]
  rw [max_eq_left (by positivity), Real.sqrt_eq_rpow]
theorem weightedLaplace_clampedSqrt_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < weightedLaplace (1 / 2) clampedSqrt u := by
  have hint := weightedLaplace_integrableOn (a := 1 / 2) (by norm_num) clampedSqrt_continuous
    abs_clampedSqrt_le u
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun v : ℝ => Real.exp (-v) * v ^ (1 / 2 : ℝ) * clampedSqrt (u * v) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    have := Real.sqrt_nonneg (2 - max (u * v) 0)
    simp only [Pi.zero_apply, clampedSqrt]
    positivity
  refine (setIntegral_pos_iff_support_of_nonneg_ae hnn hint).2 ?_
  have hε : (0 : ℝ) < 1 / (u + 1) := by positivity
  have hsub : Ioo (0 : ℝ) (1 / (u + 1)) ⊆
      Function.support (fun v : ℝ => Real.exp (-v) * v ^ (1 / 2 : ℝ) * clampedSqrt (u * v)) ∩
        Ioi 0 := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv.1
    refine ⟨?_, hv0⟩
    have h1 : u * v < 1 := by
      have h2 : v * (u + 1) < 1 := by
        have := hv.2
        rwa [lt_div_iff₀ (by positivity)] at this
      nlinarith
    have h3 : max (u * v) 0 < 2 := max_lt (by linarith) (by norm_num)
    have h4 : 0 < clampedSqrt (u * v) := Real.sqrt_pos.2 (by linarith)
    have h5 : 0 < Real.exp (-v) * v ^ (1 / 2 : ℝ) * clampedSqrt (u * v) := by positivity
    exact h5.ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  simpa using hε
theorem haarGapTail_smooth : ScaledVariables.HaarGapTailSmooth := by
  refine ⟨fun u => 2 / Real.pi * (weightedLaplace (1 / 2) cutoffSqrt u + remainderIntegral u), ?_,
    fun u hu => ?_, fun u hu => ?_⟩
  · refine contDiff_infty.2 fun n => contDiff_const.mul ?_
    exact (weightedLaplace_contDiff n _ _ (by norm_num) cutoffSqrt_contDiff
      cutoffSqrt_hasCompactSupport).add (remainderIntegral_contDiff n)
  · have h1 := weightedLaplace_clampedSqrt_pos hu
    rw [weightedLaplace_clampedSqrt_eq hu] at h1
    have : 0 < 2 / Real.pi := by positivity
    positivity
  · simp only [ScaledVariables.haarGapTail]
    rw [integral_sqrt_eq_weightedLaplace hu, weightedLaplace_clampedSqrt_eq hu]
end
end YangMills.Construction.HaarGapTailRegularity
end
