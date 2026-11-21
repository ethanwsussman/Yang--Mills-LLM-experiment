import YangMills.Construction.ComplexAnalysis.BoxIntegralHolomorphicOfDominated
import Reconstruction.Coordinates.HolomorphicParametricIntegral
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Metric Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates.ParametricIntegral
variable {n : ℕ} {O : Set (ComplexCoordinates n)}
theorem continuousAt_of_isHolomorphicIn {g : ComplexCoordinates n → ℂ}
    (hg : IsHolomorphicIn (N' := 1) O fun z _ => g z) {a : ComplexCoordinates n} (ha : a ∈ O) :
    ContinuousAt g a :=
  continuousAt_pi.1 (hg.2.1.continuousAt (hg.1.mem_nhds ha)) 0
theorem differentiableAt_comp_line {g : ComplexCoordinates n → ℂ}
    (hg : IsHolomorphicIn (N' := 1) O fun z _ => g z) (a : ComplexCoordinates n) (j : Fin n) {w : ℂ}
    (hw : a + w • stdBasisVector j ∈ O) :
    DifferentiableAt ℂ (fun t : ℂ => g (a + t • stdBasisVector j)) w := by apply _root_.YangMills.Construction.ComplexAnalysis.ParameterBox.differentiableAt_along_axis <;> assumption
theorem measurable_deriv_of_forall_ball {X : Type} [MeasurableSpace X] {F : X → ℂ → ℂ} {x : ℂ}
    {r : ℝ} (hr : 0 < r) (hF : ∀ w ∈ ball x r, Measurable fun y => F y w)
    (hd : ∀ y, DifferentiableAt ℂ (F y) x) : Measurable fun y => deriv (F y) x := by
  let h : ℕ → ℂ := fun k => ((r / (k + 2) : ℝ) : ℂ)
  have hpos : ∀ k : ℕ, 0 < r / ((k : ℝ) + 2) := fun k => by positivity
  have hnorm : ∀ k, ‖h k‖ = r / ((k : ℝ) + 2) := fun k => by
    simp only [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos k)]
  have hlt : ∀ k, ‖h k‖ < r := fun k => by
    rw [hnorm]
    exact div_lt_self hr (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hne : ∀ k, h k ≠ 0 := fun k => by
    rw [← norm_pos_iff, hnorm]
    exact hpos k
  have hlim₀ : Tendsto h atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [hnorm]
    have hk : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact hk.const_div_atTop r
  have hlim : Tendsto h atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim₀, Eventually.of_forall hne⟩
  have hmem : ∀ k, x + h k ∈ ball x r := fun k => by
    simpa [mem_ball, dist_eq_norm] using hlt k
  refine measurable_of_tendsto_metrizable
    (f := fun k y => (h k)⁻¹ • (F y (x + h k) - F y x)) (fun k => ?_) ?_
  · exact ((hF _ (hmem k)).sub (hF x (mem_ball_self hr))).const_smul (h k)⁻¹
  · exact tendsto_pi_nhds.2 fun y => (hd y).hasDerivAt.tendsto_slope_zero.comp hlim
theorem holomorphicParametricIntegral : HolomorphicParametricIntegral := by
  intro X _ μ _ n _ O hO Φ hmeas hhol hbd
  have hsm : ∀ z ∈ O, AEStronglyMeasurable (fun y => Φ (y, z)) μ :=
    fun z hz => (hmeas z hz).aestronglyMeasurable
  have hint : ∀ z ∈ O, Integrable (fun y => Φ (y, z)) μ := by
    intro z hz
    obtain ⟨U, hU, -, C, hC⟩ := hbd z hz
    exact Integrable.of_bound (hsm z hz) C
      (Eventually.of_forall fun y => hC y z (mem_of_mem_nhds hU))
  refine ⟨hint, hO, ?_, ?_⟩
  · refine continuousOn_pi.2 fun _ a ha => ?_
    obtain ⟨U, hU, hUO, C, hC⟩ := hbd a ha
    refine ContinuousAt.continuousWithinAt
      (continuousAt_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_)
    · filter_upwards [hU] with z hz using hsm z (hUO hz)
    · filter_upwards [hU] with z hz
      exact Eventually.of_forall fun y => hC y z hz
    · exact Eventually.of_forall fun y =>
        continuousAt_of_isHolomorphicIn (g := fun z => Φ (y, z)) (hhol y) ha
  · intro a ha j
    obtain ⟨U, hU, hUO, C, hC⟩ := hbd a ha
    have hline : Continuous fun w : ℂ => a + w • stdBasisVector j := by fun_prop
    have hpre : (fun w : ℂ => a + w • stdBasisVector j) ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
      hline.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
    have hr : 0 < ε / 3 := by positivity
    have hin : ∀ w ∈ ball (0 : ℂ) ε, a + w • stdBasisVector j ∈ U := fun w hw => hball hw
    have hdiff : ∀ y, ∀ w ∈ ball (0 : ℂ) ε,
        DifferentiableAt ℂ (fun t : ℂ => Φ (y, a + t • stdBasisVector j)) w := fun y w hw =>
      differentiableAt_comp_line (g := fun z => Φ (y, z)) (hhol y) a j (hUO (hin w hw))
    have hclosed : ∀ x ∈ ball (0 : ℂ) (ε / 3), closedBall x (ε / 3) ⊆ ball (0 : ℂ) ε := by
      intro x hx v hv
      rw [mem_ball, dist_zero_right] at hx ⊢
      rw [mem_closedBall, dist_eq_norm] at hv
      have := norm_add_le (v - x) x
      rw [sub_add_cancel] at this
      linarith
    have hderiv : ∀ y, ∀ x ∈ ball (0 : ℂ) (ε / 3),
        ‖deriv (fun t : ℂ => Φ (y, a + t • stdBasisVector j)) x‖ ≤ C / (ε / 3) := by
      intro y x hx
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ ?_
      · exact DifferentiableOn.diffContOnCl_ball
          (fun v hv => (hdiff y v hv).differentiableWithinAt) (hclosed x hx)
      · intro v hv
        exact hC y _ (hin v (hclosed x hx (sphere_subset_closedBall hv)))
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with x hx
    have hxε : x ∈ ball (0 : ℂ) ε := hclosed x hx (mem_closedBall_self hr.le)
    have hsub : ball x (ε / 3) ⊆ ball (0 : ℂ) ε :=
      ball_subset_closedBall.trans (hclosed x hx)
    have hmeasDeriv : Measurable fun y => deriv (fun t : ℂ => Φ (y, a + t • stdBasisVector j)) x :=
      measurable_deriv_of_forall_ball (F := fun y t => Φ (y, a + t • stdBasisVector j)) hr
        (fun w hw => hmeas _ (hUO (hin w (hsub hw)))) (fun y => hdiff y x hxε)
    have hs : ball (0 : ℂ) (ε / 3) ∈ 𝓝 x := isOpen_ball.mem_nhds hx
    have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun (t : ℂ) y => Φ (y, a + t • stdBasisVector j))
      (F' := fun (t : ℂ) y => deriv (fun t : ℂ => Φ (y, a + t • stdBasisVector j)) t)
      (bound := fun _ => C / (ε / 3)) hs
      (by
        filter_upwards [hs] with t ht
        exact hsm _ (hUO (hin t (ball_subset_ball (by linarith) ht))))
      (hint _ (hUO (hin x hxε))) hmeasDeriv.aestronglyMeasurable
      (Eventually.of_forall fun y t ht => hderiv y t ht) (integrable_const _)
      (Eventually.of_forall fun y t ht =>
        (hdiff y t ((ball_subset_ball (by linarith)) ht)).hasDerivAt)
    exact differentiableAt_pi.2 fun _ => hD.2.differentiableAt
end YangMills.Construction.Coordinates.ComplexCoordinates.ParametricIntegral
