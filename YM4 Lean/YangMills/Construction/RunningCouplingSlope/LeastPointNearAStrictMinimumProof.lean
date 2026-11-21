import YangMills.Construction.RunningCouplingSlope.LeastPointNearAStrictMinimum
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.ParametricMinima
section Restrictions
variable {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
private def derivFst (f : E × P → ℝ) (q : E × P) : E →L[ℝ] ℝ :=
  (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ E P)
private def secondDerivFst (f : E × P → ℝ) (q : E × P) : E →L[ℝ] E →L[ℝ] ℝ :=
  (fderiv ℝ (derivFst f) q).comp (ContinuousLinearMap.inl ℝ E P)
private theorem analyticAt_derivFst {f : E × P → ℝ} {q : E × P} (h : AnalyticAt ℝ f q) :
    AnalyticAt ℝ (derivFst f) q :=
  (((ContinuousLinearMap.compL ℝ E (E × P) ℝ).flip (ContinuousLinearMap.inl ℝ E P)).analyticAt _).comp h.fderiv
private theorem eventually_norm_secondDerivFst_sub_lt {f : E × P → ℝ} {q₀ : E × P} (h : AnalyticAt ℝ f q₀) {c : ℝ}
    (hc : 0 < c) :
    ∀ᶠ q in 𝓝 q₀, ‖secondDerivFst f q - secondDerivFst f q₀‖ < c := by
  filter_upwards [Metric.continuousAt_iff'.1 (analyticAt_derivFst h).fderiv.continuousAt c hc] with q hq
  rw [dist_eq_norm] at hq
  refine lt_of_le_of_lt ?_ hq
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have e : (secondDerivFst f q - secondDerivFst f q₀) v =
      (fderiv ℝ (derivFst f) q - fderiv ℝ (derivFst f) q₀) (v, 0) := rfl
  rw [e]
  refine ((fderiv ℝ (derivFst f) q - fderiv ℝ (derivFst f) q₀).le_opNorm (v, 0)).trans_eq ?_
  simp [Prod.norm_def]
private theorem hasFDerivAt_restrictFst {f : E × P → ℝ} {e : E} {p : P} (h : AnalyticAt ℝ f (e, p)) :
    HasFDerivAt (fun e' => f (e', p)) (derivFst f (e, p)) e :=
  h.differentiableAt.hasFDerivAt.comp e (hasFDerivAt_prodMk_left e p)
private theorem hasFDerivAt_derivFst_restrict {f : E × P → ℝ} {e : E} {p : P} (h : AnalyticAt ℝ f (e, p)) :
    HasFDerivAt (fun e' => derivFst f (e', p)) (secondDerivFst f (e, p)) e := by
  have h1 : HasFDerivAt (derivFst f) (fderiv ℝ (derivFst f) (e, p)) (e, p) :=
    (analyticAt_derivFst h).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun e' : E => (e', p)) (ContinuousLinearMap.inl ℝ E P) e := hasFDerivAt_prodMk_left e p
  exact HasFDerivAt.comp (g := derivFst f) (f := fun e' : E => (e', p)) e h1 h2
private theorem fderiv_fderiv_restrictFst {f : E × P → ℝ} {e : E} {p : P} (h : AnalyticAt ℝ f (e, p)) :
    fderiv ℝ (fderiv ℝ fun e' => f (e', p)) e = secondDerivFst f (e, p) := by
  have hc : Tendsto (fun e' : E => (e', p)) (𝓝 e) (𝓝 (e, p)) :=
    (continuous_id.prodMk continuous_const).tendsto e
  have e1 : (fderiv ℝ fun e' => f (e', p)) =ᶠ[𝓝 e] fun e' => derivFst f (e', p) :=
    (hc.eventually h.eventually_analyticAt).mono fun e' h' => (hasFDerivAt_restrictFst h').fderiv
  rw [e1.fderiv_eq]
  exact (hasFDerivAt_derivFst_restrict h).fderiv
private theorem exists_coercivity_const (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : ∀ v, v ≠ 0 → 0 < H v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, 2 * c * ‖v‖ ^ 2 ≤ H v v := by
  have hcont : Continuous fun v : E => H v v := H.continuous.clm_apply continuous_id
  rcases (Metric.sphere (0 : E) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have : (‖v‖⁻¹ • v) ∈ Metric.sphere (0 : E) 1 := by
        simp [norm_smul, norm_ne_zero_iff.2 hv]
      rw [he] at this
      exact this
    simp [hv]
  · obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hcont.continuousOn
    have hv₀' : v₀ ≠ 0 := by
      intro h
      rw [h] at hv₀
      simp at hv₀
    have hm := hH v₀ hv₀'
    refine ⟨H v₀ v₀ / 2, by positivity, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have hu : (‖v‖⁻¹ • v) ∈ Metric.sphere (0 : E) 1 := by
      simp [norm_smul, hn]
    have h1 : H v₀ v₀ ≤ H (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := hmin hu
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : 0 < ‖v‖ ^ 2 := by positivity
    have h3 : ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * H v v)) = H v v := by
      field_simp
    calc 2 * (H v₀ v₀ / 2) * ‖v‖ ^ 2 = ‖v‖ ^ 2 * H v₀ v₀ := by ring
      _ ≤ ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * H v v)) := mul_le_mul_of_nonneg_left h1 h2.le
      _ = H v v := h3
private theorem lt_of_secondDeriv_pos_of_deriv_zero {φ φ' φ'' : ℝ → ℝ}
    (h1 : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' τ) τ)
    (h2 : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt φ' (φ'' τ) τ) (hpos : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < φ'' τ) (h0 : φ' 0 = 0) :
    φ 0 < φ 1 := by
  have hm : StrictMonoOn φ' (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) (fun τ hτ => (h2 τ hτ).continuousAt.continuousWithinAt) fun τ hτ => ?_
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := interior_subset hτ
    rw [(h2 τ hτ').deriv]
    exact hpos τ hτ'
  have hs : StrictMonoOn φ (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) (fun τ hτ => (h1 τ hτ).continuousAt.continuousWithinAt) fun τ hτ => ?_
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := interior_subset hτ
    rw [(h1 τ hτ').deriv, ← h0]
    rw [interior_Icc] at hτ
    exact hm (left_mem_Icc.2 zero_le_one) hτ' hτ.1
  exact hs (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_lt_one
end Restrictions
theorem strictMinimumPersistsAnalytically_holds : StrictMinimumPersistsAnalytically := by
  intro E P _ _ _ _ _ _ f p₀ hf hcrit hpd
  set q₀ : E × P := (0, p₀) with hq₀
  have hg := analyticAt_derivFst hf
  set H := secondDerivFst f q₀ with hHd
  have hH : ∀ v, v ≠ 0 → 0 < H v v := by
    intro v hv
    have := hpd v hv
    rwa [fderiv_fderiv_restrictFst hf] at this
  have hg0 : derivFst f q₀ = 0 := by
    have := (hasFDerivAt_restrictFst hf).fderiv
    rw [hcrit] at this
    exact this.symm
  set Ψ : E × P → (E →L[ℝ] ℝ) × P := fun q => (derivFst f q, q.2) with hΨ
  have hΨa : AnalyticAt ℝ Ψ q₀ := hg.prod analyticAt_snd
  set D := fderiv ℝ Ψ q₀ with hD
  have hDa : HasFDerivAt Ψ ((fderiv ℝ (derivFst f) q₀).prod (ContinuousLinearMap.snd ℝ E P)) q₀ :=
    hg.differentiableAt.hasFDerivAt.prodMk hasFDerivAt_snd
  have hDe : D = (fderiv ℝ (derivFst f) q₀).prod (ContinuousLinearMap.snd ℝ E P) := hDa.fderiv
  have hinj : Function.Injective D := by
    refine (injective_iff_map_eq_zero D).2 fun q hq => ?_
    rw [hDe] at hq
    have h2 : q.2 = 0 := congrArg Prod.snd hq
    have h1 : fderiv ℝ (derivFst f) q₀ q = 0 := congrArg Prod.fst hq
    have h3 : q = (q.1, 0) := Prod.ext rfl h2
    have h4 : H q.1 = 0 := by
      show fderiv ℝ (derivFst f) q₀ (q.1, 0) = 0
      rw [← h3]
      exact h1
    by_contra hne
    have hv : q.1 ≠ 0 := fun h => hne (by rw [h3, h]; rfl)
    have := hH q.1 hv
    rw [h4] at this
    simp at this
  have hdim : Module.finrank ℝ (E × P) = Module.finrank ℝ ((E →L[ℝ] ℝ) × P) := by
    have h1 : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
      rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq]
      simp
    rw [Module.finrank_prod, Module.finrank_prod, h1]
  set i : (E × P) ≃L[ℝ] (E →L[ℝ] ℝ) × P :=
    (LinearMap.linearEquivOfInjective (D : (E × P) →ₗ[ℝ] (E →L[ℝ] ℝ) × P) hinj hdim).toContinuousLinearEquiv with hi
  have hiD : (i : (E × P) →L[ℝ] (E →L[ℝ] ℝ) × P) = D := ContinuousLinearMap.ext fun q => rfl
  have hst : HasStrictFDerivAt Ψ (i : (E × P) →L[ℝ] (E →L[ℝ] ℝ) × P) q₀ := by
    rw [hiD]
    exact hΨa.hasStrictFDerivAt
  set φ := hst.toOpenPartialHomeomorph Ψ with hφ
  have hcoe : (φ : E × P → (E →L[ℝ] ℝ) × P) = Ψ := hst.toOpenPartialHomeomorph_coe
  have hsrc : q₀ ∈ φ.source := hst.mem_toOpenPartialHomeomorph_source
  have hsym : AnalyticAt ℝ φ.symm (φ q₀) := by
    refine φ.analyticAt_symm' (i := i) hsrc (by rw [hcoe]; exact hΨa) ?_
    rw [hcoe]
    exact hiD.symm
  have hφ0 : φ q₀ = ((0 : E →L[ℝ] ℝ), p₀) := by
    rw [hcoe]
    exact Prod.ext hg0 rfl
  rw [hφ0] at hsym
  have hleft : φ.symm ((0 : E →L[ℝ] ℝ), p₀) = q₀ := by
    rw [← hφ0]
    exact φ.left_inv hsrc
  have hmap : AnalyticAt ℝ (fun p : P => φ.symm ((0 : E →L[ℝ] ℝ), p)) p₀ :=
    AnalyticAt.comp (g := φ.symm) (f := fun p : P => ((0 : E →L[ℝ] ℝ), p)) hsym (analyticAt_const.prod analyticAt_id)
  set x : P → E := fun p => (φ.symm ((0 : E →L[ℝ] ℝ), p)).1 with hx
  have hxa : AnalyticAt ℝ x p₀ := analyticAt_fst.comp hmap
  have hx0 : x p₀ = 0 := by
    simp only [hx, hleft, hq₀]
  have htgt : ∀ᶠ p in 𝓝 p₀, ((0 : E →L[ℝ] ℝ), p) ∈ φ.target := by
    have h1 : φ.target ∈ 𝓝 ((0 : E →L[ℝ] ℝ), p₀) := by
      rw [← hφ0]
      exact φ.open_target.mem_nhds (φ.map_source hsrc)
    have h2 : Tendsto (fun p : P => ((0 : E →L[ℝ] ℝ), p)) (𝓝 p₀) (𝓝 ((0 : E →L[ℝ] ℝ), p₀)) :=
      (continuous_const.prodMk continuous_id).tendsto p₀
    exact h2.eventually h1
  have hcritp : ∀ᶠ p in 𝓝 p₀, derivFst f (x p, p) = 0 := by
    filter_upwards [htgt] with p hp
    have h1 := φ.right_inv hp
    rw [hcoe] at h1
    have h2 : (φ.symm ((0 : E →L[ℝ] ℝ), p)).2 = p := congrArg Prod.snd h1
    have h3 : derivFst f (φ.symm ((0 : E →L[ℝ] ℝ), p)) = 0 := congrArg Prod.fst h1
    have h4 : φ.symm ((0 : E →L[ℝ] ℝ), p) = (x p, p) := Prod.ext rfl h2
    rwa [h4] at h3
  obtain ⟨c, hc, hfloor⟩ := exists_coercivity_const H hH
  have hK : ∀ᶠ q in 𝓝 q₀, ‖secondDerivFst f q - H‖ < c := eventually_norm_secondDerivFst_sub_lt hf hc
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hK.and hf.eventually_analyticAt)
  have hpos : ∀ q ∈ Metric.ball q₀ r, ∀ v, v ≠ 0 → 0 < secondDerivFst f q v v := by
    intro q hq v hv
    have h1 := (hball q hq).1
    have h2 := hfloor v
    have h3 : |(secondDerivFst f q - H) v v| ≤ ‖secondDerivFst f q - H‖ * ‖v‖ * ‖v‖ :=
      ((secondDerivFst f q - H) v).le_of_opNorm_le ((secondDerivFst f q - H).le_opNorm v) v
    have h4 : 0 < ‖v‖ ^ 2 := by
      have := norm_pos_iff.2 hv
      positivity
    have h5 : ‖secondDerivFst f q - H‖ * ‖v‖ * ‖v‖ ≤ c * ‖v‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1.le h4.le
      nlinarith
    have h6 := (abs_le.1 (h3.trans h5)).1
    have h7 : (secondDerivFst f q - H) v v = secondDerivFst f q v v - H v v := by simp
    rw [h7] at h6
    nlinarith
  have hxs : ∀ᶠ p in 𝓝 p₀, ‖x p‖ < r := by
    have h1 : Tendsto (fun p => ‖x p‖) (𝓝 p₀) (𝓝 0) := by
      have := hxa.continuousAt.tendsto.norm
      simpa [hx0] using this
    exact h1.eventually (gt_mem_nhds hr)
  have hpr : ∀ᶠ p in 𝓝 p₀, dist p p₀ < r := Metric.eventually_nhds_iff_ball.2 ⟨r, hr, fun p hp => hp⟩
  refine ⟨x, r, hr, hxa, hx0, ?_⟩
  filter_upwards [hcritp, hxs, hpr] with p hp1 hp2 hp3
  have hin : ∀ e : E, ‖e‖ < r → (e, p) ∈ Metric.ball q₀ r := by
    intro e he
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa [hq₀] using he, hp3⟩
  refine ⟨hp2, fun e he hne => ?_, fun v hv => ?_⟩
  · set d := e - x p with hd
    have hd0 : d ≠ 0 := sub_ne_zero.2 hne
    have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, ‖x p + τ • d‖ < r := by
      intro τ hτ
      have h1 : x p + τ • d = (1 - τ) • x p + τ • e := by
        simp only [hd, smul_sub, sub_smul, one_smul]
        abel
      rw [h1]
      have hb := (convex_ball (0 : E) r)
      have h2 := hb (show x p ∈ Metric.ball (0 : E) r by simpa using hp2)
        (show e ∈ Metric.ball (0 : E) r by simpa using he) (sub_nonneg.2 hτ.2) hτ.1 (by ring)
      simpa using h2
    have hline : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => x p + τ • d) d τ := fun τ => by
      have h2 : HasDerivAt (fun τ : ℝ => τ • d) ((1 : ℝ) • d) τ := (hasDerivAt_id τ).smul_const d
      rw [one_smul] at h2
      exact h2.const_add (x p)
    have han : ∀ τ ∈ Icc (0 : ℝ) 1, AnalyticAt ℝ f (x p + τ • d, p) := fun τ hτ =>
      (hball _ (hin _ (hseg τ hτ))).2
    have hinc := lt_of_secondDeriv_pos_of_deriv_zero (φ := fun τ : ℝ => f (x p + τ • d, p))
      (φ' := fun τ : ℝ => derivFst f (x p + τ • d, p) d)
      (φ'' := fun τ : ℝ => secondDerivFst f (x p + τ • d, p) d d)
      (fun τ hτ => HasFDerivAt.comp_hasDerivAt (l := fun e' => f (e', p)) (f := fun τ : ℝ => x p + τ • d) τ
        (hasFDerivAt_restrictFst (han τ hτ)) (hline τ))
      (fun τ hτ => by
        have h1 := HasFDerivAt.comp_hasDerivAt (l := fun e' => derivFst f (e', p))
          (f := fun τ : ℝ => x p + τ • d) τ (hasFDerivAt_derivFst_restrict (han τ hτ)) (hline τ)
        have h2 := h1.clm_apply (hasDerivAt_const τ d)
        simpa using h2)
      (fun τ hτ => hpos _ (hin _ (hseg τ hτ)) d hd0)
      (by simp [hp1])
    simpa [hd] using hinc
  · rw [fderiv_fderiv_restrictFst (hball _ (hin _ hp2)).2]
    exact hpos _ (hin _ hp2) v hv
end YangMills.Construction.ParametricMinima
end
