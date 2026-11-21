import YangMills.Construction.ComplexAnalysis.HolomorphicAndRealAnalyticFacts
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Mathlib
open Filter Set Metric MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.ComplexAnalysis
open YangMills.Construction.Coordinates
namespace HolomorphicAndRealAnalyticFacts
theorem differentiableOn_integral_of_bounded {X : Type} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {U : Set ℂ} {g : ℂ → X → ℂ} (hU : IsOpen U)
    (hbdd : ∃ B : ℝ, ∀ s ∈ U, ∀ x, ‖g s x‖ ≤ B)
    (hmeas : Measurable (fun p : U × X => g p.1 p.2))
    (hdiff : ∀ x, DifferentiableOn ℂ (fun s => g s x) U) :
    DifferentiableOn ℂ (fun s => ∫ x, g s x ∂μ) U := by
  obtain ⟨B, hB⟩ := hbdd
  intro s₀ hs₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU s₀ hs₀
  have hδ : 0 < ε / 3 := by positivity
  have hsub : ball s₀ (ε / 3) ⊆ U := fun t ht =>
    hball (ball_subset_ball (by linarith) ht)
  have hslice : ∀ s ∈ U, Measurable (g s) := fun s hs => by
    have hpair : Measurable (fun x : X => ((⟨s, hs⟩ : U), x)) :=
      measurable_const.prodMk measurable_id
    exact hmeas.comp hpair
  have hderiv : ∀ x, ∀ t ∈ U, HasDerivAt (fun s => g s x) (deriv (fun s => g s x) t) t :=
    fun x t ht => ((hdiff x).differentiableAt (hU.mem_nhds ht)).hasDerivAt
  have hcauchy : ∀ x, ∀ t ∈ ball s₀ (ε / 3), ‖deriv (fun s => g s x) t‖ ≤ B / (ε / 3) := by
    intro x t ht
    have hclosed : closedBall t (ε / 3) ⊆ ball s₀ ε := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball] at ht ⊢
      have htri := dist_triangle w t s₀
      linarith
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ ?_ ?_
    · exact DifferentiableOn.diffContOnCl_ball ((hdiff x).mono (hclosed.trans hball)) (subset_rfl)
    · intro w hw
      exact hB w (hball (hclosed (sphere_subset_closedBall hw))) x
  have hmeasDeriv : Measurable (fun x => deriv (fun s => g s x) s₀) := by
    let v : ℕ → ℝ := fun k => ε / 3 * (1 / ((k : ℝ) + 1))
    have hvpos : ∀ k, 0 < v k := fun k => by positivity
    have hvle : ∀ k, v k ≤ ε / 3 := fun k => by
      have hle : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      exact mul_le_of_le_one_right hδ.le hle
    have hv0 : Tendsto v atTop (𝓝 0) := by
      simpa [v] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 3)
    have hvc : Tendsto (fun k => (v k : ℂ)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
      · simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hv0
      · simpa using (hvpos k).ne'
    have hmem : ∀ k, s₀ + (v k : ℂ) ∈ U := fun k => by
      refine hball ?_
      rw [mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hvpos k)]
      linarith [hvle k]
    refine measurable_of_tendsto_metrizable
      (f := fun k x => ((v k : ℂ))⁻¹ • (g (s₀ + (v k : ℂ)) x - g s₀ x)) (fun k => ?_) ?_
    · exact ((hslice _ (hmem k)).sub (hslice _ hs₀)).const_smul ((v k : ℂ))⁻¹
    · refine tendsto_pi_nhds.2 fun x => ?_
      exact (hasDerivAt_iff_tendsto_slope_zero.1 (hderiv x s₀ hs₀)).comp hvc
  have hint : Integrable (g s₀) μ := by
    refine Integrable.of_bound (hslice s₀ hs₀).aestronglyMeasurable B ?_
    exact Eventually.of_forall (hB s₀ hs₀)
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := g)
    (F' := fun t x => deriv (fun s => g s x) t) (x₀ := s₀) (s := ball s₀ (ε / 3))
    (bound := fun _ => B / (ε / 3)) (ball_mem_nhds s₀ hδ)
    (by
      filter_upwards [ball_mem_nhds s₀ hδ] with t ht
      exact (hslice t (hsub ht)).aestronglyMeasurable)
    hint hmeasDeriv.aestronglyMeasurable
    (Eventually.of_forall fun x t ht => hcauchy x t ht) (integrable_const _)
    (Eventually.of_forall fun x t ht => hderiv x t (hsub ht))
  exact hdom.2.differentiableAt.differentiableWithinAt
theorem eq_zero_of_locally_holomorphic_of_eqOn_Ioo {φ : ℝ → ℂ}
    (hloc : ∀ t₀ : ℝ, ∃ ρ > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball (t₀ : ℂ) ρ) ∧
      ∀ t : ℝ, (t : ℂ) ∈ Metric.ball (t₀ : ℂ) ρ → h t = φ t)
    (hIoo : ∃ a b : ℝ, a < b ∧ ∀ t ∈ Ioo a b, φ t = 0) (t : ℝ) : φ t = 0 := by
  let Z : Set ℝ := {t | ∀ᶠ s in 𝓝 t, φ s = 0}
  have hopen : IsOpen Z := isOpen_setOfPred_eventually_nhds
  have hne : Z.Nonempty := by
    obtain ⟨a, b, hab, hab0⟩ := hIoo
    refine ⟨(a + b) / 2, ?_⟩
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    filter_upwards [Ioo_mem_nhds hmid.1 hmid.2] with s hs using hab0 s hs
  have hclosed : IsClosed Z := by
    refine isClosed_of_closure_subset fun t₁ ht₁ => ?_
    obtain ⟨ρ, hρ, h, hh, heq⟩ := hloc t₁
    obtain ⟨s₁, hs₁, hs₁Z⟩ := mem_closure_iff_nhds.1 ht₁ (ball t₁ ρ) (ball_mem_nhds _ hρ)
    have hmem : ∀ s : ℝ, s ∈ ball t₁ ρ → (s : ℂ) ∈ ball (t₁ : ℂ) ρ := fun s hs => by
      have hdist : dist (s : ℂ) (t₁ : ℂ) = dist s t₁ := by
        rw [dist_eq_norm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
      rw [mem_ball] at hs ⊢
      rwa [hdist]
    have han : AnalyticOnNhd ℂ h (ball (t₁ : ℂ) ρ) := hh.analyticOnNhd isOpen_ball
    have hfreq : ∃ᶠ w in 𝓝[≠] (s₁ : ℂ), h w = 0 := by
      have hs₁Z' : ∀ᶠ s : ℝ in 𝓝 s₁, φ s = 0 := hs₁Z
      have hev : ∀ᶠ s : ℝ in 𝓝[≠] s₁, h (s : ℂ) = 0 := by
        refine nhdsWithin_le_nhds ?_
        filter_upwards [hs₁Z', isOpen_ball.mem_nhds hs₁] with s hs hsb
        rw [heq s (hmem s hsb), hs]
      have htend : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] s₁) (𝓝[≠] (s₁ : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · exact (Complex.continuous_ofReal.tendsto s₁).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          simpa using hs
      exact htend.frequently hev.frequently
    have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball _ _).isPreconnected (hmem s₁ hs₁) hfreq
    change ∀ᶠ s in 𝓝 t₁, φ s = 0
    filter_upwards [ball_mem_nhds t₁ hρ] with s hs
    rw [← heq s (hmem s hs)]
    exact hzero (hmem s hs)
  have hZ : Z = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  have ht : t ∈ Z := hZ ▸ mem_univ t
  exact (show ∀ᶠ s : ℝ in 𝓝 t, φ s = 0 from ht).self_of_nhds
theorem exists_holomorphic_extension
    (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {k : ℕ}
    {U : Set (ComplexCoordinates k)} {f : ComplexCoordinates k → ℂ}
    (hf : ComplexCoordinates.IsRealAnalyticIn (N' := 1) U (fun z _ => f z))
    {c : ComplexCoordinates k} (hc : c ∈ U) :
    ∃ (W : Set (ComplexCoordinates k)) (h : ComplexCoordinates k → ℂ),
      IsOpen W ∧ c ∈ W ∧ W ∩ ComplexCoordinates.realLocus k ⊆ U ∧
      ComplexCoordinates.IsHolomorphicIn (N' := 1) W (fun z _ => h z) ∧
      ∀ z ∈ W ∩ ComplexCoordinates.realLocus k, h z = f z := by
  obtain ⟨⟨V, hV, rfl⟩, hser⟩ := hf
  obtain ⟨coef, hcoef⟩ := hser c hc
  obtain ⟨η₁, hη₁, hball₁⟩ := Metric.isOpen_iff.1 hV c hc.1
  obtain ⟨η₂, hη₂, hball₂⟩ := Metric.mem_nhdsWithin_iff.1 hcoef
  obtain ⟨ρ, hρ, hρ₁, hρ₂⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < η₁ ∧ ρ < η₂ :=
    ⟨min η₁ η₂ / 2, by positivity,
      by linarith [min_le_left η₁ η₂, lt_min hη₁ hη₂],
      by linarith [min_le_right η₁ η₂, lt_min hη₁ hη₂]⟩
  let monomial : (Fin k → ℕ) → ComplexCoordinates k → ComplexCoordinates 1 :=
    fun m z => (∏ j, (z j - c j) ^ m j) • coef m
  have hsumAt : ∀ z ∈ ball c η₂ ∩ ComplexCoordinates.realLocus k,
      HasSum (fun m => monomial m z) (fun _ => f z) := fun z hz => hball₂ hz
  let corner : ComplexCoordinates k := fun j => c j + (ρ : ℂ)
  have hcornerDist : ∀ j, ‖corner j - c j‖ = ρ := fun j => by
    simp [corner, abs_of_pos hρ]
  have hcorner : corner ∈ ball c η₂ ∩ ComplexCoordinates.realLocus k := by
    refine ⟨?_, fun j => ?_⟩
    · rw [mem_ball, dist_pi_lt_iff hη₂]
      intro j
      rw [dist_eq_norm, hcornerDist]
      exact hρ₂
    · have hcj := hc.2 j
      simp [corner, hcj]
  have hsummable : Summable fun m => ‖monomial m corner‖ :=
    summable_norm_iff.2 (hsumAt corner hcorner).summable
  have hdom : ∀ m, ∀ z ∈ ball c ρ, ‖monomial m z‖ ≤ ‖monomial m corner‖ := by
    intro m z hz
    rw [mem_ball, dist_pi_lt_iff hρ] at hz
    simp only [monomial, norm_smul, norm_prod, norm_pow]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    rw [hcornerDist]
    have hzj := hz j
    rw [dist_eq_norm] at hzj
    exact hzj.le
  have hunif := tendstoUniformlyOn_tsum hsummable (fun m z hz => hdom m z hz)
  obtain ⟨u, hu⟩ := (atTop : Filter (Finset (Fin k → ℕ))).exists_seq_tendsto
  have hpoly : ∀ t : Finset (Fin k → ℕ),
      Differentiable ℂ (fun z : ComplexCoordinates k => ∑ m ∈ t, monomial m z) := by
    intro t
    simp only [monomial]
    fun_prop
  have hpartial : ∀ n, ComplexCoordinates.IsHolomorphicIn (ball c ρ)
      (fun z : ComplexCoordinates k => ∑ m ∈ u n, monomial m z) := by
    intro n
    refine ⟨isOpen_ball, (hpoly _).continuous.continuousOn, fun y _ j => ?_⟩
    refine Eventually.of_forall fun ζ => ?_
    have hline : Differentiable ℂ
        (fun ζ : ℂ => y + ζ • ComplexCoordinates.stdBasisVector j) := by fun_prop
    exact ((hpoly (u n)).comp hline) ζ
  have hlimit : ComplexCoordinates.IsHolomorphicIn (ball c ρ)
      (fun z : ComplexCoordinates k => ∑' m, monomial m z) :=
    (H.1 k (ball c ρ) isOpen_ball).2 1 (fun n z => ∑ m ∈ u n, monomial m z) _ hpartial
      (fun v hv => hu.eventually (hunif v hv))
  refine ⟨ball c ρ, fun z => (∑' m, monomial m z) 0, isOpen_ball, mem_ball_self hρ, ?_, ?_, ?_⟩
  · rintro z ⟨hz, hzr⟩
    exact ⟨hball₁ (ball_subset_ball hρ₁.le hz), hzr⟩
  · have hfun : (fun (z : ComplexCoordinates k) (_ : Fin 1) => (∑' m, monomial m z) 0)
        = fun z => ∑' m, monomial m z := by
      funext z i
      rw [Subsingleton.elim i 0]
    exact hfun ▸ hlimit
  · rintro z ⟨hz, hzr⟩
    have htsum := (hsumAt z ⟨ball_subset_ball hρ₂.le hz, hzr⟩).tsum_eq
    simp only [htsum]
end HolomorphicAndRealAnalyticFacts
open HolomorphicAndRealAnalyticFacts in
theorem holomorphicAndRealAnalyticFacts
    (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    HolomorphicAndRealAnalyticFacts :=
  ⟨fun _ _ μ _ _ _ hU hbdd hmeas hdiff => differentiableOn_integral_of_bounded μ hU hbdd hmeas hdiff,
    fun _ hloc hIoo t => eq_zero_of_locally_holomorphic_of_eqOn_Ioo hloc hIoo t,
    fun _ _ _ _ hf _ hc => exists_holomorphic_extension H hf hc⟩
end YangMills.Construction.ComplexAnalysis
