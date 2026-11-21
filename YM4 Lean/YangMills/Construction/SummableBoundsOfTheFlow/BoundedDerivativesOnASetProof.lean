import YangMills.Construction.SummableBoundsOfTheFlow.BoundedDerivativesOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace YangMills.Construction.UniformDerivativeBounds
theorem abs_le_of_bounded {n : ℕ} {D : ℝ} {S : Set ℝ} {f : ℝ → ℝ} (hf : UniformlyBoundedDerivs n D S f) :
    ∀ x ∈ S, |f x| ≤ D := by
  cases n with
  | zero => exact hf.1
  | succ n => exact hf.1
theorem bounded_mono (n : ℕ) : ∀ (D D' : ℝ) (S : Set ℝ) (f : ℝ → ℝ), D ≤ D' → UniformlyBoundedDerivs n D S f →
    UniformlyBoundedDerivs n D' S f := by
  induction n with
  | zero =>
    intro D D' S f hD hf
    exact ⟨fun x hx => (hf.1 x hx).trans hD, hf.2⟩
  | succ n ih =>
    intro D D' S f hD hf
    obtain ⟨b, f', hd, hn⟩ := hf
    exact ⟨fun x hx => (b x hx).trans hD, f', hd, ih _ _ _ _ hD hn⟩
theorem bounded_of_succ (n : ℕ) : ∀ (D : ℝ) (S : Set ℝ) (f : ℝ → ℝ), UniformlyBoundedDerivs (n + 1) D S f →
    UniformlyBoundedDerivs n D S f := by
  induction n with
  | zero =>
    intro D S f hf
    obtain ⟨b, f', hd, -⟩ := hf
    exact ⟨b, fun x hx => (hd x hx).continuousAt.continuousWithinAt⟩
  | succ n ih =>
    intro D S f hf
    obtain ⟨b, f', hd, hn⟩ := hf
    exact ⟨b, f', hd, ih _ _ _ hn⟩
theorem bounded_congr (n : ℕ) : ∀ (D : ℝ) (S : Set ℝ) (f g : ℝ → ℝ), IsOpen S → (∀ x ∈ S, f x = g x) →
    UniformlyBoundedDerivs n D S f → UniformlyBoundedDerivs n D S g := by
  cases n with
  | zero =>
    intro D S f g _ he hf
    exact ⟨fun x hx => by rw [← he x hx]; exact hf.1 x hx, hf.2.congr fun x hx => (he x hx).symm⟩
  | succ n =>
    intro D S f g hS he hf
    obtain ⟨b, f', hd, hn⟩ := hf
    refine ⟨fun x hx => by rw [← he x hx]; exact b x hx, f', fun x hx => ?_, hn⟩
    refine (hd x hx).congr_of_eventuallyEq ?_
    filter_upwards [hS.mem_nhds hx] with y hy using (he y hy).symm
theorem bounded_mono_set (n : ℕ) : ∀ (D : ℝ) (S T : Set ℝ) (f : ℝ → ℝ), T ⊆ S → UniformlyBoundedDerivs n D S f →
    UniformlyBoundedDerivs n D T f := by
  induction n with
  | zero =>
    intro D S T f hs hf
    exact ⟨fun x hx => hf.1 x (hs hx), hf.2.mono hs⟩
  | succ n ih =>
    intro D S T f hs hf
    obtain ⟨b, f', hd, hn⟩ := hf
    exact ⟨fun x hx => b x (hs hx), f', fun x hx => hd x (hs hx), ih _ _ _ _ hs hn⟩
theorem bounded_zero (n : ℕ) : ∀ (D : ℝ) (S : Set ℝ), 0 ≤ D → UniformlyBoundedDerivs n D S fun _ => 0 := by
  induction n with
  | zero =>
    intro D S hD
    exact ⟨fun x _ => by simpa using hD, continuousOn_const⟩
  | succ n ih =>
    intro D S hD
    exact ⟨fun x _ => by simpa using hD, fun _ => 0, fun x _ => hasDerivAt_const x _, ih _ _ hD⟩
theorem bounded_const (n : ℕ) (S : Set ℝ) (c : ℝ) : UniformlyBoundedDerivs n |c| S fun _ => c := by
  cases n with
  | zero => exact ⟨fun x _ => le_rfl, continuousOn_const⟩
  | succ n =>
    exact ⟨fun x _ => le_rfl, fun _ => 0, fun x _ => hasDerivAt_const x _, bounded_zero n _ _ (abs_nonneg c)⟩
theorem bounded_add (n : ℕ) : ∀ (D D' : ℝ) (S : Set ℝ) (f g : ℝ → ℝ), UniformlyBoundedDerivs n D S f →
    UniformlyBoundedDerivs n D' S g → UniformlyBoundedDerivs n (D + D') S fun x => f x + g x := by
  induction n with
  | zero =>
    intro D D' S f g hf hg
    exact ⟨fun x hx => (abs_add_le _ _).trans (add_le_add (hf.1 x hx) (hg.1 x hx)), hf.2.add hg.2⟩
  | succ n ih =>
    intro D D' S f g hf hg
    obtain ⟨b, f', hd, hn⟩ := hf
    obtain ⟨b', g', gd, gn⟩ := hg
    exact ⟨fun x hx => (abs_add_le _ _).trans (add_le_add (b x hx) (b' x hx)), fun x => f' x + g' x,
      fun x hx => (hd x hx).add (gd x hx), ih _ _ _ _ _ hn gn⟩
theorem bounded_mul (n : ℕ) : ∀ (D D' : ℝ) (S : Set ℝ) (f g : ℝ → ℝ), 0 ≤ D → 0 ≤ D' →
    UniformlyBoundedDerivs n D S f → UniformlyBoundedDerivs n D' S g →
    UniformlyBoundedDerivs n (2 ^ n * D * D') S fun x => f x * g x := by
  induction n with
  | zero =>
    intro D D' S f g h0 h0' hf hg
    refine ⟨fun x hx => ?_, hf.2.mul hg.2⟩
    rw [abs_mul, pow_zero, one_mul]
    exact mul_le_mul (hf.1 x hx) (hg.1 x hx) (abs_nonneg _) h0
  | succ n ih =>
    intro D D' S f g h0 h0' hf hg
    have hfl := bounded_of_succ n _ _ _ hf
    have hgl := bounded_of_succ n _ _ _ hg
    obtain ⟨b, f', hd, hn⟩ := hf
    obtain ⟨b', g', gd, gn⟩ := hg
    refine ⟨fun x hx => ?_, fun x => f' x * g x + f x * g' x, fun x hx => (hd x hx).mul (gd x hx), ?_⟩
    · rw [abs_mul]
      have h1 : |f x| * |g x| ≤ D * D' := mul_le_mul (b x hx) (b' x hx) (abs_nonneg _) h0
      have h2 : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      have h3 : 0 ≤ D * D' := mul_nonneg h0 h0'
      calc _ ≤ D * D' := h1
        _ ≤ 2 ^ (n + 1) * (D * D') := le_mul_of_one_le_left h3 h2
        _ = _ := by ring
    · have e := bounded_add n _ _ S _ _ (ih D D' S f' g h0 h0' hn hgl) (ih D D' S f g' h0 h0' hfl gn)
      refine bounded_mono n _ _ _ _ (le_of_eq ?_) e
      ring
theorem bounded_exp (n : ℕ) : ∀ D : ℝ, 0 ≤ D → ∃ D' : ℝ, 0 ≤ D' ∧ ∀ (S : Set ℝ) (f : ℝ → ℝ),
    UniformlyBoundedDerivs n D S f → UniformlyBoundedDerivs n D' S fun x => Real.exp (f x) := by
  induction n with
  | zero =>
    intro D hD
    refine ⟨Real.exp D, (Real.exp_pos _).le, fun S f hf => ⟨fun x hx => ?_, Real.continuous_exp.comp_continuousOn hf.2⟩⟩
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hf.1 x hx))
  | succ n ih =>
    intro D hD
    obtain ⟨E, hE, hEs⟩ := ih D hD
    refine ⟨max (Real.exp D) (2 ^ n * E * D), le_max_of_le_left (Real.exp_pos _).le, fun S f hf => ?_⟩
    have hfl := bounded_of_succ n _ _ _ hf
    obtain ⟨b, f', hd, hn⟩ := hf
    refine ⟨fun x hx => ?_, fun x => Real.exp (f x) * f' x, fun x hx => (hd x hx).exp, ?_⟩
    · rw [abs_of_pos (Real.exp_pos _)]
      exact le_max_of_le_left (Real.exp_le_exp.2 ((le_abs_self _).trans (b x hx)))
    · exact bounded_mono n _ _ _ _ (le_max_right _ _) (bounded_mul n E D S _ _ hE hD (hEs S f hfl) hn)
theorem hasDerivAt_iteratedDeriv_of_contDiffAt {g : ℝ → ℝ} {n : ℕ} {t : ℝ} (h : ContDiffAt ℝ (n + 1 : ℕ) g t) :
    HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g t) t := by
  have h1 : DifferentiableAt ℝ (iteratedDeriv n g) t := by
    have h2 : iteratedDeriv n g = fun x => iteratedFDeriv ℝ n g x (fun _ => 1) :=
      funext fun _ => iteratedDeriv_eq_iteratedFDeriv
    have h3 := h.differentiableAt_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n)
    rw [h2]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ) ℝ (fun _ => 1)).differentiableAt.comp t h3
  rw [iteratedDeriv_succ]
  exact h1.hasDerivAt
theorem bounded_iteratedDeriv (n : ℕ) : ∀ (m : ℕ) (D : ℝ) (S : Set ℝ) (e : ℝ → ℝ), IsOpen S →
    (∀ x ∈ S, ContDiffAt ℝ (m + n : ℕ) e x) → (∀ j, j ≤ m + n → ∀ x ∈ S, |iteratedDeriv j e x| ≤ D) →
    UniformlyBoundedDerivs n D S (iteratedDeriv m e) := by
  induction n with
  | zero =>
    intro m D S e hS hc hb
    refine ⟨hb m le_rfl, ?_⟩
    have h1 : ContDiffOn ℝ m e S := fun x hx => (hc x hx).contDiffWithinAt
    have h2 := h1.continuousOn_iteratedDerivWithin (m := m) (by exact_mod_cast le_rfl) hS.uniqueDiffOn
    exact h2.congr fun x hx => (iteratedDerivWithin_of_isOpen hS hx).symm
  | succ n ih =>
    intro m D S e hS hc hb
    refine ⟨hb m (by omega), iteratedDeriv (m + 1) e, fun x hx => ?_, ?_⟩
    · exact hasDerivAt_iteratedDeriv_of_contDiffAt ((hc x hx).of_le (by exact_mod_cast (show m + 1 ≤ m + (n + 1) by omega)))
    · refine ih (m + 1) D S e hS (fun x hx => ?_) fun j hj x hx => hb j (by omega) x hx
      have : m + 1 + n = m + (n + 1) := by omega
      rw [this]
      exact hc x hx
theorem contDiffOn_of_bounded (n : ℕ) : ∀ (D : ℝ) (S : Set ℝ) (f : ℝ → ℝ), IsOpen S → UniformlyBoundedDerivs n D S f →
    ContDiffOn ℝ n f S := by
  induction n with
  | zero =>
    intro D S f _ hf
    exact contDiffOn_zero.2 hf.2
  | succ n ih =>
    intro D S f hS hf
    obtain ⟨b, f', hd, hn⟩ := hf
    have : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [this, contDiffOn_succ_iff_deriv_of_isOpen hS]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih D S f' hS hn).congr fun x hx => (hd x hx).deriv
theorem hasDerivAt_zero_of_abs_le_flat {Q C : ℝ → ℝ} {D x : ℝ} (hb : ∀ y, |Q y| ≤ D * |C y|) (hC : HasDerivAt C 0 x)
    (h0 : C x = 0) : HasDerivAt Q 0 x := by
  have hQ0 : Q x = 0 := by
    have := hb x
    rw [h0, abs_zero, mul_zero] at this
    exact abs_nonpos_iff.1 this
  rw [hasDerivAt_iff_isLittleO] at hC ⊢
  refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound D ?_) hC
  refine Eventually.of_forall fun y => ?_
  simp only [hQ0, h0, sub_zero, smul_zero, Real.norm_eq_abs]
  exact hb y
theorem contDiff_top_deriv {C : ℝ → ℝ} (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv C) := ((contDiff_infty_iff_deriv).1 hC).2
theorem bounded_indicator_mul_flat (n : ℕ) : ∀ (D B : ℝ) (I S : Set ℝ) (f C : ℝ → ℝ), IsOpen S → S ⊆ I → 0 ≤ D → 0 ≤ B →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C → (∀ x ∈ I \ S, ∀ j : ℕ, iteratedDeriv j C x = 0) →
    (∀ j, j ≤ n → ∀ x ∈ I, |iteratedDeriv j C x| ≤ B) → UniformlyBoundedDerivs n D S f →
    UniformlyBoundedDerivs n (2 ^ n * D * B) I (S.indicator fun x => f x * C x) := by
  have hQb : ∀ (n : ℕ) (D : ℝ) (S : Set ℝ) (f C : ℝ → ℝ), 0 ≤ D → UniformlyBoundedDerivs n D S f →
      ∀ y, |S.indicator (fun x => f x * C x) y| ≤ D * |C y| := by
    intro n D S f C hD hf y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_le_of_bounded hf y hy) (abs_nonneg _)
    · rw [indicator_of_notMem hy, abs_zero]
      positivity
  have hI : ∀ (n : ℕ) (D B : ℝ) (I S : Set ℝ) (f C : ℝ → ℝ), S ⊆ I → 0 ≤ D → 0 ≤ B →
      (∀ x ∈ I, |C x| ≤ B) → UniformlyBoundedDerivs n D S f →
      ∀ y ∈ I, |S.indicator (fun x => f x * C x) y| ≤ 2 ^ n * D * B := by
    intro n D B I S f C _ hD hB hc hf y hy
    have h1 := hQb n D S f C hD hf y
    have h2 : D * |C y| ≤ D * B := mul_le_mul_of_nonneg_left (hc y hy) hD
    have h3 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h4 : 0 ≤ D * B := mul_nonneg hD hB
    calc _ ≤ D * B := h1.trans h2
      _ ≤ 2 ^ n * (D * B) := le_mul_of_one_le_left h4 h3
      _ = _ := by ring
  induction n with
  | zero =>
    intro D B I S f C hS hSI hD hB hC hflat hb hf
    have hc0 : ∀ x ∈ I, |C x| ≤ B := fun x hx => by simpa using hb 0 le_rfl x hx
    refine ⟨hI 0 D B I S f C hSI hD hB hc0 hf, fun x hx => ContinuousAt.continuousWithinAt ?_⟩
    by_cases hxS : x ∈ S
    · have h1 : ContinuousAt (fun y => f y * C y) x :=
        ((hf.2.continuousAt (hS.mem_nhds hxS))).mul
          (hC.continuous.continuousAt)
      refine h1.congr ?_
      filter_upwards [hS.mem_nhds hxS] with y hy
      rw [indicator_of_mem hy]
    · have h0 : C x = 0 := by simpa using hflat x ⟨hx, hxS⟩ 0
      have hlim : Tendsto (fun y => D * |C y|) (𝓝 x) (𝓝 0) := by
        have : ContinuousAt (fun y => D * |C y|) x := (hC.continuous.abs.const_mul D |>.continuousAt)
        simpa [ContinuousAt, h0] using this
      have ht : Tendsto (S.indicator fun y => f y * C y) (𝓝 x) (𝓝 0) :=
        squeeze_zero_norm (fun y => by simpa using hQb 0 D S f C hD hf y) hlim
      rw [ContinuousAt, indicator_of_notMem hxS]
      exact ht
  | succ n ih =>
    intro D B I S f C hS hSI hD hB hC hflat hb hf
    have hc0 : ∀ x ∈ I, |C x| ≤ B := fun x hx => by simpa using hb 0 (by omega) x hx
    have hbound := hI (n + 1) D B I S f C hSI hD hB hc0 hf
    have hall := hQb (n + 1) D S f C hD hf
    have hfl := bounded_of_succ n _ _ _ hf
    obtain ⟨b, f', hd, hn⟩ := hf
    have hdC : ∀ x, HasDerivAt C (deriv C x) x := fun x =>
      ((hC.differentiable (by simp)) x).hasDerivAt
    refine ⟨hbound, fun x => S.indicator (fun y => f' y * C y) x + S.indicator (fun y => f y * deriv C y) x,
      fun x hx => ?_, ?_⟩
    · beta_reduce
      by_cases hxS : x ∈ S
      · rw [indicator_of_mem hxS, indicator_of_mem hxS]
        refine ((hd x hxS).mul (hdC x)).congr_of_eventuallyEq ?_
        filter_upwards [hS.mem_nhds hxS] with y hy
        rw [indicator_of_mem hy]
        rfl
      · rw [indicator_of_notMem hxS, indicator_of_notMem hxS, add_zero]
        have h0 : C x = 0 := by simpa using hflat x ⟨hx, hxS⟩ 0
        have h1 : deriv C x = 0 := by simpa using hflat x ⟨hx, hxS⟩ 1
        have := hdC x
        rw [h1] at this
        exact hasDerivAt_zero_of_abs_le_flat hall this h0
    · have e1 := ih D B I S f' C hS hSI hD hB hC hflat (fun j hj => hb j (by omega)) hn
      have e2 := ih D B I S f (deriv C) hS hSI hD hB (contDiff_top_deriv hC)
        (fun x hx j => by
          rw [← iteratedDeriv_succ']
          exact hflat x hx (j + 1))
        (fun j hj x hx => by
          rw [← iteratedDeriv_succ']
          exact hb (j + 1) (by omega) x hx) hfl
      refine bounded_mono n _ _ _ _ (le_of_eq ?_) (bounded_add n _ _ I _ _ e1 e2)
      ring
theorem aestronglyMeasurable_of_hasDerivAt {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {S : Set ℝ}
    {Q Q' : ℝ → Ω → ℝ} {t : ℝ}
    (hS : IsOpen S) (ht : t ∈ S) (hm : ∀ y ∈ S, AEStronglyMeasurable (Q y) μ)
    (hd : ∀ᵐ ω ∂μ, HasDerivAt (fun y => Q y ω) (Q' t ω) t) : AEStronglyMeasurable (Q' t) μ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hS t ht
  set h : ℕ → ℝ := fun m => δ / (m + 2) with hh
  have hpos : ∀ m, 0 < h m := fun m => by simp only [hh]; positivity
  have hsmall : ∀ m, t + h m ∈ S := by
    intro m
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (hpos m)]
    simp only [hh]
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hlim : Tendsto h atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun m => (hpos m).ne')
    have h1 : Tendsto (fun m : ℕ => ((m : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact h1.const_div_atTop δ
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun m ω => (h m)⁻¹ • (Q (t + h m) ω - Q t ω)) (fun m => ?_) ?_
  · exact ((hm _ (hsmall m)).sub (hm _ ht)).const_smul ((h m)⁻¹)
  · filter_upwards [hd] with ω hω
    exact (hasDerivAt_iff_tendsto_slope_zero.1 hω).comp hlim
theorem bounded_integral {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ (D : ℝ) (S : Set ℝ) (Q : ℝ → Ω → ℝ), IsOpen S →
    (∀ᵐ ω ∂μ, UniformlyBoundedDerivs n D S fun t => Q t ω) → (∀ t ∈ S, AEStronglyMeasurable (Q t) μ) →
    UniformlyBoundedDerivs n (D * μ.real univ) S fun t => ∫ ω, Q t ω ∂μ := by
  have hb : ∀ (n : ℕ) (D : ℝ) (S : Set ℝ) (Q : ℝ → Ω → ℝ),
      (∀ᵐ ω ∂μ, UniformlyBoundedDerivs n D S fun t => Q t ω) →
      ∀ t ∈ S, |∫ ω, Q t ω ∂μ| ≤ D * μ.real univ := by
    intro n D S Q h t ht
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := Q t) (C := D)
      (by filter_upwards [h] with ω hω using by simpa using abs_le_of_bounded hω t ht)
    simpa using this
  induction n with
  | zero =>
    intro D S Q hS h hm
    refine ⟨hb 0 D S Q h, fun t ht => ContinuousAt.continuousWithinAt ?_⟩
    refine continuousAt_of_dominated (bound := fun _ => D) ?_ ?_ (integrable_const _) ?_
    · filter_upwards [hS.mem_nhds ht] with y hy using hm y hy
    · filter_upwards [hS.mem_nhds ht] with y hy
      filter_upwards [h] with ω hω
      simpa using hω.1 y hy
    · filter_upwards [h] with ω hω
      exact hω.2.continuousAt (hS.mem_nhds ht)
  | succ n ih =>
    intro D S Q hS h hm
    set Q' : ℝ → Ω → ℝ := fun t ω => deriv (fun y => Q y ω) t with hQ'
    have hder : ∀ᵐ ω ∂μ, ∀ y ∈ S, HasDerivAt (fun y => Q y ω) (Q' y ω) y := by
      filter_upwards [h] with ω hω y hy
      obtain ⟨-, f', hd, -⟩ := hω
      exact (hd y hy).differentiableAt.hasDerivAt
    have hn' : ∀ᵐ ω ∂μ, UniformlyBoundedDerivs n D S fun t => Q' t ω := by
      filter_upwards [h] with ω hω
      obtain ⟨-, f', hd, hn⟩ := hω
      exact bounded_congr n D S f' _ hS (fun y hy => (hd y hy).deriv.symm) hn
    have hm' : ∀ y ∈ S, AEStronglyMeasurable (Q' y) μ := fun y hy =>
      aestronglyMeasurable_of_hasDerivAt hS hy hm (by filter_upwards [hder] with ω hω using hω y hy)
    refine ⟨hb (n + 1) D S Q h, fun t => ∫ ω, Q' t ω ∂μ, fun t ht => ?_, ih D S Q' hS hn' hm'⟩
    have hint : Integrable (Q t) μ := by
      refine Integrable.of_bound (hm t ht) D ?_
      filter_upwards [h] with ω hω
      simpa using abs_le_of_bounded hω t ht
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := Q) (F' := Q') (bound := fun _ => D)
      (hS.mem_nhds ht) (by filter_upwards [hS.mem_nhds ht] with y hy using hm y hy) hint (hm' t ht)
      (by
        filter_upwards [hn'] with ω hω y hy
        simpa using abs_le_of_bounded hω y hy)
      (integrable_const _) (by filter_upwards [hder] with ω hω y hy using hω y hy)).2
theorem closureProperties_holds : closureProperties_statement where
  mono := bounded_mono
  of_succ := bounded_of_succ
  congr := bounded_congr
  mono_set := bounded_mono_set
  const := bounded_const
  add := bounded_add
  mul := bounded_mul
  exp := bounded_exp
  of_contDiff := by
    intro n D S e hS hc hb
    have := bounded_iteratedDeriv n 0 D S e hS (fun x hx => by simpa using hc x hx)
      (fun j hj x hx => hb j (by omega) x hx)
    simpa using this
  contDiffOn := contDiffOn_of_bounded
  indicator_mul_flat := bounded_indicator_mul_flat
  integral := fun Ω _ μ _ n => bounded_integral μ n
end YangMills.Construction.UniformDerivativeBounds
end
