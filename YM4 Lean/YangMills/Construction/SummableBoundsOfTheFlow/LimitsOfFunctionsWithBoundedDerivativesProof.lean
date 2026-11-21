import YangMills.Construction.SummableBoundsOfTheFlow.LimitsOfFunctionsWithBoundedDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace YangMills.Construction.UniformLimits
variable {k : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
private theorem norm_sub_sub_fderiv_le_of_lipschitz {f : (Fin k → ℝ) → F}
    {f' : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] F} {U : Set (Fin k → ℝ)}
    {B : ℝ} (hB : 0 ≤ B) (hU : Convex ℝ U) (hf : ∀ x ∈ U, HasFDerivAt f (f' x) x)
    (hlip : ∀ x ∈ U, ∀ y ∈ U, ‖f' x - f' y‖ ≤ B * ‖x - y‖) {x y : Fin k → ℝ} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f y - f x - f' x (y - x)‖ ≤ B * ‖y - x‖ * ‖y - x‖ := by
  have hseg : segment ℝ x y ⊆ U := hU.segment_subset hx hy
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := f) (f' := f') (φ := f' x)
    (s := segment ℝ x y) (fun z hz => (hf z (hseg hz)).hasFDerivWithinAt) (fun z hz => ?_)
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  refine (hlip z (hseg hz) x hx).trans (mul_le_mul_of_nonneg_left ?_ hB)
  obtain ⟨t, ht0, ht1, rfl⟩ := (segment_eq_image_lineMap ℝ x y ▸ hz : z ∈ AffineMap.lineMap x y '' Icc (0 : ℝ) 1) |>
    fun ⟨t, ht, e⟩ => (⟨t, ht.1, ht.2, e⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap x y t = z)
  have hline : AffineMap.lineMap x y t - x = t • (y - x) := by
    simp [AffineMap.lineMap_apply]
  rw [hline, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  exact mul_le_of_le_one_left (norm_nonneg _) ht1
private theorem opNorm_le_sum_norm_apply_basis (A : (Fin k → ℝ) →L[ℝ] F) :
    ‖A‖ ≤ ∑ i, ‖A (Pi.single i 1)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun x => ?_
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc ‖A x‖ = ‖∑ i, x i • A (Pi.single i 1)‖ := by
        conv_lhs => rw [hx]
        simp [map_sum, map_smul]
    _ ≤ ∑ i, ‖x i • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * ‖A (Pi.single i 1)‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]
private theorem norm_pi_single_one (i : Fin k) : ‖(Pi.single i (1 : ℝ) : Fin k → ℝ)‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hji : j = i
    · subst hji
      simp
    · simp [Pi.single_apply, hji]
  · simpa using norm_le_pi_norm (Pi.single i (1 : ℝ) : Fin k → ℝ) i
private theorem exists_hasFDerivAt_of_tendsto_of_lipschitz_fderiv [CompleteSpace F] {ι : Type} {l : Filter ι}
    [l.NeBot] {U : Set (Fin k → ℝ)} (hUo : IsOpen U)
    (hUc : Convex ℝ U) {B : ℝ} (hB : 0 ≤ B) {f : ι → (Fin k → ℝ) → F}
    {f' : ι → (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] F} {g : (Fin k → ℝ) → F}
    (hf : ∀ᶠ n in l, (∀ x ∈ U, HasFDerivAt (f n) (f' n x) x) ∧
      ∀ x ∈ U, ∀ y ∈ U, ‖f' n x - f' n y‖ ≤ B * ‖x - y‖)
    (hg : ∀ x ∈ U, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    ∃ g' : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] F, (∀ x ∈ U, Tendsto (fun n => f' n x) l (𝓝 (g' x))) ∧
      ∀ x ∈ U, HasFDerivAt g (g' x) x := by
  have hpairs : ∀ y ∈ U, ∀ δ : ℝ, 0 < δ → ∀ᶠ p : ι × ι in l ×ˢ l, ‖f p.1 y - f p.2 y‖ < δ := by
    intro y hy δ hδ
    have h1 : Tendsto (fun p : ι × ι => f p.1 y - f p.2 y) (l ×ˢ l) (𝓝 (g y - g y)) :=
      ((hg y hy).comp tendsto_fst).sub ((hg y hy).comp tendsto_snd)
    rw [sub_self] at h1
    have h2 := h1.norm
    rw [norm_zero] at h2
    exact h2.eventually (gt_mem_nhds hδ)
  have hcauchy : ∀ x ∈ U, Cauchy (map (fun n => f' n x) l) := by
    intro x hx
    rw [cauchy_map_iff]
    refine ⟨‹l.NeBot›, ?_⟩
    refine (Metric.uniformity_basis_dist.tendsto_right_iff).2 fun ε hε => ?_
    obtain ⟨h₀, hh₀, hsub⟩ := Metric.isOpen_iff.mp hUo x hx
    set h : ℝ := min (h₀ / 2) (ε / (8 * (k + 1) * (B + 1))) with hh
    have hpos : 0 < h := lt_min (by positivity) (by positivity)
    have hle : h ≤ ε / (8 * (k + 1) * (B + 1)) := min_le_right _ _
    set δ : ℝ := ε * h / (8 * (k + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    have hmem : ∀ i : Fin k, x + h • (Pi.single i (1 : ℝ) : Fin k → ℝ) ∈ U := by
      intro i
      apply hsub
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hpos,
        norm_pi_single_one i, mul_one]
      have := min_le_left (h₀ / 2) (ε / (8 * (k + 1) * (B + 1)))
      linarith
    have hev₁ : ∀ᶠ p : ι × ι in l ×ˢ l, ∀ i : Fin k,
        ‖f p.1 (x + h • (Pi.single i (1 : ℝ) : Fin k → ℝ)) - f p.2 (x + h • (Pi.single i (1 : ℝ) : Fin k → ℝ))‖ < δ :=
      eventually_all.2 fun i => hpairs _ (hmem i) δ hδpos
    have hev₂ := hpairs x hx δ hδpos
    have hev₃ : ∀ᶠ p : ι × ι in l ×ˢ l, _ := hf.prod_mk hf
    filter_upwards [hev₁, hev₂, hev₃] with p p₁ p₂ p₃
    obtain ⟨⟨d₁, l₁⟩, d₂, l₂⟩ := p₃
    show dist (f' p.1 x) (f' p.2 x) < ε
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (opNorm_le_sum_norm_apply_basis _) ?_
    have heach : ∀ i : Fin k, ‖(f' p.1 x - f' p.2 x) (Pi.single i 1)‖ ≤ ε / (2 * (k + 1)) := by
      intro i
      set e : Fin k → ℝ := Pi.single i 1 with he
      have hne : ‖e‖ = 1 := norm_pi_single_one i
      have hy := hmem i
      have t₁ := norm_sub_sub_fderiv_le_of_lipschitz hB hUc d₁ l₁ hx hy
      have t₂ := norm_sub_sub_fderiv_le_of_lipschitz hB hUc d₂ l₂ hx hy
      have hdd : x + h • e - x = h • e := add_sub_cancel_left _ _
      have hnn : ‖h • e‖ = h := by rw [norm_smul, hne, Real.norm_eq_abs, abs_of_pos hpos, mul_one]
      rw [hdd, hnn] at t₁ t₂
      have a₁ := p₁ i
      have hsum : h * ‖(f' p.1 x - f' p.2 x) e‖ ≤ 2 * δ + 2 * (B * h * h) := by
        have e₁ : h * ‖(f' p.1 x - f' p.2 x) e‖ = ‖f' p.1 x (h • e) - f' p.2 x (h • e)‖ := by
          rw [map_smul, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
          rfl
        rw [e₁]
        have e₂ : f' p.1 x (h • e) - f' p.2 x (h • e) =
            (f p.1 (x + h • e) - f p.2 (x + h • e)) - (f p.1 x - f p.2 x) -
              (f p.1 (x + h • e) - f p.1 x - f' p.1 x (h • e)) +
              (f p.2 (x + h • e) - f p.2 x - f' p.2 x (h • e)) := by abel
        rw [e₂]
        refine (norm_add_le _ _).trans ?_
        refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
        refine (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans ?_
        linarith [a₁.le, p₂.le, t₁, t₂]
      have hBh : B * h ≤ ε / (8 * (k + 1)) := by
        calc B * h ≤ (B + 1) * (ε / (8 * (k + 1) * (B + 1))) :=
              mul_le_mul (by linarith) hle hpos.le (by linarith)
          _ = _ := by field_simp
      have h3 : ‖(f' p.1 x - f' p.2 x) e‖ ≤ 2 * δ / h + 2 * (B * h) := by
        rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
        nlinarith
      have h4 : 2 * δ / h = ε / (4 * (k + 1)) := by
        simp only [hδ]
        field_simp
        ring
      rw [h4] at h3
      have h5 : ε / (4 * (k + 1)) + 2 * (ε / (8 * (k + 1))) = ε / (2 * (k + 1)) := by
        field_simp
        ring
      linarith
    calc ∑ i, ‖(f' p.1 x - f' p.2 x) (Pi.single i 1)‖ ≤ ∑ _i : Fin k, ε / (2 * (k + 1)) :=
          Finset.sum_le_sum fun i _ => heach i
      _ = k * (ε / (2 * (k + 1))) := by simp
      _ < ε := by
        have : (k : ℝ) * (ε / (2 * (k + 1))) = ε * (k / (2 * (k + 1))) := by ring
        rw [this]
        have h6 : (k : ℝ) / (2 * (k + 1)) < 1 := by
          rw [div_lt_one (by positivity)]
          have : (0 : ℝ) ≤ k := by positivity
          linarith
        nlinarith
  classical
  have hlim : ∀ x, ∃ A, x ∈ U → Tendsto (fun n => f' n x) l (𝓝 A) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨A, hA⟩ := cauchy_map_iff_exists_tendsto.mp (hcauchy x hx)
      exact ⟨A, fun _ => hA⟩
    · exact ⟨0, fun hxU => absurd hxU hx⟩
  choose g' hg' using hlim
  refine ⟨g', fun x hx => hg' x hx, fun x hx => ?_⟩
  have hbound : ∀ y ∈ U, ‖g y - g x - g' x (y - x)‖ ≤ B * ‖y - x‖ * ‖y - x‖ := by
    intro y hy
    have h1 : Tendsto (fun n => ‖f n y - f n x - f' n x (y - x)‖) l (𝓝 ‖g y - g x - g' x (y - x)‖) := by
      refine (((hg y hy).sub (hg x hx)).sub ?_).norm
      exact ((ContinuousLinearMap.apply ℝ F (y - x)).continuous.tendsto _).comp (hg' x hx)
    refine le_of_tendsto h1 ?_
    filter_upwards [hf] with n hn using norm_sub_sub_fderiv_le_of_lipschitz hB hUc hn.1 hn.2 hx hy
  rw [hasFDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hU : U ∈ 𝓝 x := hUo.mem_nhds hx
  have hsmall : ∀ᶠ y in 𝓝 x, B * ‖y - x‖ ≤ c := by
    have h1 : Tendsto (fun y => B * ‖y - x‖) (𝓝 x) (𝓝 (B * ‖x - x‖)) :=
      (continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto x
    rw [sub_self, norm_zero, mul_zero] at h1
    exact (h1.eventually (gt_mem_nhds hc)).mono fun y hy => hy.le
  filter_upwards [hU, hsmall] with y hy hs
  exact (hbound y hy).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
theorem iteratedFDeriv_tendsto_of_uniform_limit : IteratedFDerivTendstoOfUniformLimit := by
  intro k r B ι l _ W Q hr hev hun j v hj
  have hU : IsOpen (Metric.ball (0 : Fin k → ℝ) r) := Metric.isOpen_ball
  have hC : Convex ℝ (Metric.ball (0 : Fin k → ℝ) r) := convex_ball _ _
  have h0 : (0 : Fin k → ℝ) ∈ Metric.ball (0 : Fin k → ℝ) r := Metric.mem_ball_self hr
  have hB : 0 ≤ B := by
    obtain ⟨n, hn⟩ := hev.exists
    exact (norm_nonneg _).trans (hn.2 0 h0 0 (by norm_num))
  have hpw : ∀ x ∈ Metric.ball (0 : Fin k → ℝ) r, Tendsto (fun n => W n x) l (𝓝 (Q x)) := fun x hx =>
    hun.tendsto_at hx
  have hfirst : ∀ᶠ n in l, (∀ x ∈ Metric.ball (0 : Fin k → ℝ) r, HasFDerivAt (W n) (fderiv ℝ (W n) x) x) ∧
      ∀ x ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ y ∈ Metric.ball (0 : Fin k → ℝ) r,
        ‖fderiv ℝ (W n) x - fderiv ℝ (W n) y‖ ≤ B * ‖x - y‖ := by
    filter_upwards [hev] with n hn
    have c2 : ContDiffOn ℝ 2 (fderiv ℝ (W n)) (Metric.ball 0 r) := hn.1.fderiv_of_isOpen hU (by norm_num)
    refine ⟨fun x hx => ((hn.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt, ?_⟩
    intro x hx y hy
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fderiv ℝ (W n))
      (f' := fderiv ℝ (fderiv ℝ (W n))) (fun z hz =>
        ((c2.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
      (fun z hz => ?_) hC hy hx
    have := hn.2 z hz 2 (by norm_num)
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this
  obtain ⟨g₁, t₁, d₁⟩ := exists_hasFDerivAt_of_tendsto_of_lipschitz_fderiv hU hC hB hfirst hpw
  have hsecond : ∀ᶠ n in l, (∀ x ∈ Metric.ball (0 : Fin k → ℝ) r,
        HasFDerivAt (fderiv ℝ (W n)) (fderiv ℝ (fderiv ℝ (W n)) x) x) ∧
      ∀ x ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ y ∈ Metric.ball (0 : Fin k → ℝ) r,
        ‖fderiv ℝ (fderiv ℝ (W n)) x - fderiv ℝ (fderiv ℝ (W n)) y‖ ≤ B * ‖x - y‖ := by
    filter_upwards [hev] with n hn
    have c2 : ContDiffOn ℝ 2 (fderiv ℝ (W n)) (Metric.ball 0 r) := hn.1.fderiv_of_isOpen hU (by norm_num)
    have c1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ (W n))) (Metric.ball 0 r) := c2.fderiv_of_isOpen hU (by norm_num)
    refine ⟨fun x hx => ((c2.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt, ?_⟩
    intro x hx y hy
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fderiv ℝ (fderiv ℝ (W n)))
      (f' := fderiv ℝ (fderiv ℝ (fderiv ℝ (W n)))) (fun z hz =>
        ((c1.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
      (fun z hz => ?_) hC hy hx
    have := hn.2 z hz 3 le_rfl
    rwa [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this
  obtain ⟨g₂, t₂, d₂⟩ := exists_hasFDerivAt_of_tendsto_of_lipschitz_fderiv hU hC hB hsecond t₁
  have e₁ : ∀ x ∈ Metric.ball (0 : Fin k → ℝ) r, fderiv ℝ Q x = g₁ x := fun x hx => (d₁ x hx).fderiv
  have e₂ : fderiv ℝ (fderiv ℝ Q) 0 = g₂ 0 := by
    have h1 : fderiv ℝ Q =ᶠ[𝓝 0] g₁ := by
      filter_upwards [hU.mem_nhds h0] with x hx using e₁ x hx
    exact ((d₂ 0 h0).congr_of_eventuallyEq h1).fderiv
  interval_cases j
  · simpa [iteratedFDeriv_zero_apply] using hpw 0 h0
  · simp only [iteratedFDeriv_one_apply]
    rw [e₁ 0 h0]
    exact ((ContinuousLinearMap.apply ℝ ℝ (v 0)).continuous.tendsto _).comp (t₁ 0 h0)
  · simp only [iteratedFDeriv_two_apply]
    rw [e₂]
    have h1 := ((ContinuousLinearMap.apply ℝ ((Fin k → ℝ) →L[ℝ] ℝ) (v 0)).continuous.tendsto _).comp (t₂ 0 h0)
    exact ((ContinuousLinearMap.apply ℝ ℝ (v 1)).continuous.tendsto _).comp h1
end YangMills.Construction.UniformLimits
end
