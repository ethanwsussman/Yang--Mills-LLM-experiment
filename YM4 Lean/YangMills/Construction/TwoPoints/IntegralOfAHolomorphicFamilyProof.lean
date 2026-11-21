import YangMills.Construction.TwoPoints.EntireContinuationInTheRotationAngleProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Metric Filter Topology Set
noncomputable section
namespace YangMills.Construction.TwoPoints.HolomorphicParametricIntegral
theorem isHolomorphicOnOne_iff_differentiableOn {U : Set ℂ} (hU : IsOpen U) (f : ℂ → ℂ) :
    IsHolomorphicOnOne U f ↔ DifferentiableOn ℂ f U := by apply _root_.YangMills.Construction.TwoPoints.EntireAngleContinuationProof.isHolomorphicOnOne_iff_differentiableOn <;> assumption
theorem norm_deriv_le_of_closedBall_bound {U : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {c : ℂ} {r M : ℝ} (hr : 0 < r) (hsub : Metric.closedBall c (2 * r) ⊆ U)
    (hM : ∀ z ∈ Metric.closedBall c (2 * r), ‖f z‖ ≤ M) {z : ℂ} (hz : z ∈ ball c r) :
    ‖deriv f z‖ ≤ M / r := by
  have hin : Metric.closedBall z r ⊆ Metric.closedBall c (2 * r) := by
    refine closedBall_subset_closedBall' ?_
    have := mem_ball.1 hz
    linarith
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ fun w hw => ?_
  · exact (hf.mono (hin.trans hsub)).diffContOnCl_ball subset_rfl
  · exact hM w (hin (sphere_subset_closedBall hw))
theorem measurable_deriv_of_family {α : Type} [MeasurableSpace α] {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → α → ℂ} (hmeas : ∀ z ∈ U, Measurable (F z))
    (hdiff : ∀ x, DifferentiableOn ℂ (fun z => F z x) U)
    {c : ℂ} (hc : c ∈ U) : Measurable fun x => deriv (fun z => F z x) c := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU c hc
  let h : ℕ → ℂ := fun n => ((ε / 2 / (n + 1) : ℝ) : ℂ)
  have hpos : ∀ n : ℕ, 0 < ε / 2 / ((n : ℝ) + 1) := fun n => by positivity
  have hne : ∀ n, h n ≠ 0 := fun n => Complex.ofReal_ne_zero.2 (hpos n).ne'
  have hsmall : ∀ n, ‖h n‖ < ε := fun n => by
    have hle : ε / 2 / ((n : ℝ) + 1) ≤ ε / 2 :=
      div_le_self (by positivity) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    simp only [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
    linarith
  have htend : Tendsto h atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hne⟩
    have h0 : Tendsto (fun n : ℕ => ε / 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 2) |>.congr
        (fun n => by ring)
    have h1 := (Complex.continuous_ofReal.tendsto 0).comp h0
    simpa [h, Function.comp_def] using h1
  have hmem : ∀ n, c + h n ∈ U := fun n => hball (by
    simpa [mem_ball, dist_eq_norm] using hsmall n)
  refine measurable_of_tendsto_metrizable
    (f := fun n x => (h n)⁻¹ • (F (c + h n) x - F c x)) (fun n => ?_) ?_
  · change Measurable fun x => (h n)⁻¹ * (F (c + h n) x - F c x)
    exact ((hmeas _ (hmem n)).sub (hmeas _ hc)).const_mul _
  · refine tendsto_pi_nhds.2 fun x => ?_
    have hd : HasDerivAt (fun z => F z x) (deriv (fun z => F z x) c) c :=
      ((hdiff x c hc).differentiableAt (hU.mem_nhds hc)).hasDerivAt
    exact hd.tendsto_slope_zero.comp htend
theorem statement_holds : HolomorphicParametricIntegral.Statement := by
  intro X _ μ U hU F hmeas hholo hdom
  have hdiff : ∀ x : X, DifferentiableOn ℂ (fun z => F z x) U := fun x =>
    (isHolomorphicOnOne_iff_differentiableOn hU _).1 (hholo x)
  have hint : ∀ z ∈ U, Integrable (F z) μ := by
    intro z hz
    obtain ⟨g, -, hg, hle⟩ := hdom {z} isCompact_singleton (singleton_subset_iff.2 hz)
    exact hg.mono' (hmeas z hz).aestronglyMeasurable
      (Eventually.of_forall fun x => hle z rfl x)
  refine ⟨hint, (isHolomorphicOnOne_iff_differentiableOn hU _).2 fun c hc => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hc)
  have hr : 0 < ε / 2 := by positivity
  have hsub : Metric.closedBall c (2 * (ε / 2)) ⊆ U := by
    rwa [mul_div_cancel₀ ε two_ne_zero]
  obtain ⟨g, -, hg, hle⟩ := hdom _ (isCompact_closedBall c (2 * (ε / 2))) hsub
  have hballU : ball c (ε / 2) ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hsub
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (x₀ := c)
    (s := ball c (ε / 2)) (bound := fun x => g x / (ε / 2))
    (F' := fun z x => deriv (fun w => F w x) z) (ball_mem_nhds c hr)
    (by
      filter_upwards [hU.mem_nhds hc] with z hz
      exact (hmeas z hz).aestronglyMeasurable)
    (hint c hc)
    (measurable_deriv_of_family hU (fun z hz => hmeas z hz) hdiff hc).aestronglyMeasurable
    (Eventually.of_forall fun x z hz =>
      norm_deriv_le_of_closedBall_bound (hdiff x) hr hsub (fun w hw => hle w hw x) hz)
    (hg.div_const _)
    (Eventually.of_forall fun x z hz =>
      ((hdiff x z (hballU hz)).differentiableAt (hU.mem_nhds (hballU hz))).hasDerivAt)
  exact hderiv.2.differentiableAt.differentiableWithinAt
end YangMills.Construction.TwoPoints.HolomorphicParametricIntegral
end
