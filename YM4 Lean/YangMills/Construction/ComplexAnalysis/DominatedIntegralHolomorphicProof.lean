import YangMills.Construction.ComplexAnalysis.BoxIntegralHolomorphicOfDominated
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import Mathlib
set_option autoImplicit false
open Filter Set Topology MeasureTheory Metric
namespace YangMills.Construction
open Coordinates Coordinates.ComplexCoordinates
namespace ComplexAnalysis
namespace DominatedIntegral
variable {n : ℕ}
lemma continuous_line (a : ComplexCoordinates n) (j : Fin n) :
    Continuous fun ζ : ℂ => a + ζ • stdBasisVector j := by
  fun_prop
lemma differentiableAt_line_of_shift {u : ComplexCoordinates n → ℂ} {a : ComplexCoordinates n}
    {j : Fin n} {ζ : ℂ} (h : DifferentiableAt ℂ
      (fun ξ : ℂ => u (a + ζ • stdBasisVector j + ξ • stdBasisVector j)) 0) :
    DifferentiableAt ℂ (fun ξ : ℂ => u (a + ξ • stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.differentiableAt_line_of_translate <;> assumption
lemma differentiableAt_along_line {U : Set (ComplexCoordinates n)} {u : ComplexCoordinates n → ℂ}
    (hu : IsHolomorphicIn (N' := 1) U fun z _ => u z) {a : ComplexCoordinates n} (j : Fin n)
    {ζ : ℂ} (hζ : a + ζ • stdBasisVector j ∈ U) :
    DifferentiableAt ℂ (fun ξ : ℂ => u (a + ξ • stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.ComplexAnalysis.ParameterBox.differentiableAt_along_axis <;> assumption
lemma integrable_deriv_and_hasDerivAt_line {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Set (ComplexCoordinates n)} (hU : IsOpen U)
    {g : ComplexCoordinates n → Ω → ℂ} {G : Ω → ℝ}
    (hmeas : ∀ z ∈ U, Measurable (g z))
    (hhol : ∀ ω, IsHolomorphicIn (N' := 1) U fun z _ => g z ω)
    (hbound : ∀ z ∈ U, ∀ ω, ‖g z ω‖ ≤ G ω)
    (hint : Integrable G μ) {z : ComplexCoordinates n} (hz : z ∈ U) (j : Fin n) :
    Integrable (fun ω => deriv (fun ζ : ℂ => g (z + ζ • stdBasisVector j) ω) 0) μ ∧
      HasDerivAt (fun ζ : ℂ => ∫ ω, g (z + ζ • stdBasisVector j) ω ∂μ)
        (∫ ω, deriv (fun ζ : ℂ => g (z + ζ • stdBasisVector j) ω) 0 ∂μ) 0 := by
  have hopen : IsOpen ((fun ζ : ℂ => z + ζ • stdBasisVector j) ⁻¹' U) :=
    hU.preimage (continuous_line z j)
  have h0 : (0 : ℂ) ∈ (fun ζ : ℂ => z + ζ • stdBasisVector j) ⁻¹' U := by
    simpa using hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / 3 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hclosed : ∀ ζ : ℂ, ‖ζ‖ ≤ 2 * δ → z + ζ • stdBasisVector j ∈ U := by
    intro ζ hζ
    have hmem : ζ ∈ ball (0 : ℂ) ε := by
      rw [mem_ball_zero_iff]
      rw [hδdef] at hζ
      linarith
    exact hball hmem
  have hdiff : ∀ (ω : Ω) (ζ : ℂ), z + ζ • stdBasisVector j ∈ U →
      DifferentiableAt ℂ (fun ξ : ℂ => g (z + ξ • stdBasisVector j) ω) ζ :=
    fun ω ζ h => differentiableAt_along_line (hhol ω) j h
  have hnear : ∀ ζ ξ : ℂ, ‖ζ‖ < δ → ξ ∈ closedBall ζ δ → ‖ξ‖ ≤ 2 * δ := by
    intro ζ ξ hζ hξ
    have h1 : ‖ξ - ζ‖ ≤ δ := by simpa [dist_eq_norm] using hξ
    have h2 := norm_le_norm_add_norm_sub' ξ ζ
    linarith
  have hcauchy : ∀ (ω : Ω) (ζ : ℂ), ‖ζ‖ < δ →
      ‖deriv (fun ξ : ℂ => g (z + ξ • stdBasisVector j) ω) ζ‖ ≤ G ω / δ := by
    intro ω ζ hζ
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ ?_ ?_
    · have hon : DifferentiableOn ℂ (fun ξ : ℂ => g (z + ξ • stdBasisVector j) ω)
          (closedBall ζ δ) := fun ξ hξ =>
        (hdiff ω ξ (hclosed ξ (hnear ζ ξ hζ hξ))).differentiableWithinAt
      exact hon.diffContOnCl_ball subset_rfl
    · intro ξ hξ
      exact hbound _ (hclosed ξ (hnear ζ ξ hζ (sphere_subset_closedBall hξ))) ω
  have hzero : ‖(0 : ℂ)‖ ≤ 2 * δ := by simpa using (by positivity : 0 ≤ 2 * δ)
  obtain ⟨t, htdef⟩ : ∃ t : ℕ → ℝ, t = fun p : ℕ => δ * (1 / ((p : ℝ) + 1)) := ⟨_, rfl⟩
  have htpos : ∀ p, 0 < t p := by
    intro p
    rw [htdef]
    positivity
  have htle : ∀ p, t p ≤ δ := by
    intro p
    rw [htdef]
    refine mul_le_of_le_one_right hδ.le ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have httend : Tendsto t atTop (𝓝 0) := by
    rw [htdef]
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  have htnorm : ∀ p, ‖((t p : ℝ) : ℂ)‖ ≤ 2 * δ := by
    intro p
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos p)]
    linarith [htle p]
  have hmeasderiv : Measurable
      (fun ω => deriv (fun ξ : ℂ => g (z + ξ • stdBasisVector j) ω) 0) := by
    refine measurable_of_tendsto_metrizable
      (f := fun (p : ℕ) ω => ((t p : ℝ) : ℂ)⁻¹ •
        (g (z + ((0 : ℂ) + ((t p : ℝ) : ℂ)) • stdBasisVector j) ω -
          g (z + (0 : ℂ) • stdBasisVector j) ω)) ?_ ?_
    · intro p
      have h1 := hmeas _ (hclosed ((0 : ℂ) + ((t p : ℝ) : ℂ)) (by simpa using htnorm p))
      have h2 := hmeas _ (hclosed 0 hzero)
      exact (h1.sub h2).const_smul (((t p : ℝ) : ℂ)⁻¹)
    · rw [tendsto_pi_nhds]
      intro ω
      have hd := (hdiff ω 0 (hclosed 0 hzero)).hasDerivAt
      have hs := hasDerivAt_iff_tendsto_slope_zero.1 hd
      refine hs.comp ?_
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun p => ?_⟩
      · simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp httend
      · simpa using (htpos p).ne'
  have hF_meas : ∀ᶠ ζ in 𝓝 (0 : ℂ), AEStronglyMeasurable
      (fun ω => g (z + ζ • stdBasisVector j) ω) μ := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with ζ hζ
    have hζ' : ‖ζ‖ < δ := by simpa using hζ
    exact (hmeas _ (hclosed ζ (by linarith))).aestronglyMeasurable
  have hF_int : Integrable (fun ω => g (z + (0 : ℂ) • stdBasisVector j) ω) μ :=
    hint.mono' (hmeas _ (hclosed 0 hzero)).aestronglyMeasurable
      (ae_of_all _ (hbound _ (hclosed 0 hzero)))
  have h_bound : ∀ᵐ ω ∂μ, ∀ ζ ∈ ball (0 : ℂ) δ,
      ‖deriv (fun ξ : ℂ => g (z + ξ • stdBasisVector j) ω) ζ‖ ≤ G ω / δ :=
    ae_of_all _ fun ω ζ hζ => hcauchy ω ζ (by simpa using hζ)
  have h_diff : ∀ᵐ ω ∂μ, ∀ ζ ∈ ball (0 : ℂ) δ,
      HasDerivAt (fun ξ : ℂ => g (z + ξ • stdBasisVector j) ω)
        (deriv (fun ξ : ℂ => g (z + ξ • stdBasisVector j) ω) ζ) ζ := by
    refine ae_of_all _ fun ω ζ hζ => ?_
    have hζ' : ‖ζ‖ < δ := by simpa using hζ
    exact (hdiff ω ζ (hclosed ζ (by linarith))).hasDerivAt
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := μ)
    (F := fun ζ ω => g (z + ζ • stdBasisVector j) ω)
    (F' := fun ζ ω => deriv (fun ξ : ℂ => g (z + ξ • stdBasisVector j) ω) ζ)
    (x₀ := 0) (s := ball (0 : ℂ) δ) (bound := fun ω => G ω / δ)
    (ball_mem_nhds 0 hδ) hF_meas hF_int hmeasderiv.aestronglyMeasurable h_bound
    (hint.div_const δ) h_diff
end DominatedIntegral
open DominatedIntegral in
theorem dominatedIntegralHolomorphicAndDeriv : DominatedIntegralHolomorphicAndDeriv := by
  unfold DominatedIntegralHolomorphicAndDeriv
  intro Ω _ μ n _ U hU g G hmeas hhol hbound hint
  have hline := fun (z : ComplexCoordinates n) (hz : z ∈ U) (j : Fin n) =>
    integrable_deriv_and_hasDerivAt_line hU hmeas hhol hbound hint hz j
  refine ⟨⟨hU, ?_, ?_⟩, fun z hz j => ⟨(hline z hz j).1, (hline z hz j).2.deriv⟩⟩
  · refine continuousOn_pi.2 fun _ => ?_
    refine continuousOn_of_dominated (bound := G)
      (fun z hz => (hmeas z hz).aestronglyMeasurable)
      (fun z hz => ae_of_all _ (hbound z hz)) hint (ae_of_all _ fun ω => ?_)
    exact (continuous_apply (0 : Fin 1)).comp_continuousOn (hhol ω).2.1
  · intro a ha j
    have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • stdBasisVector j ∈ U :=
      (continuous_line a j).continuousAt.eventually (hU.mem_nhds (by simpa using ha))
    filter_upwards [hnear] with ζ hζ
    refine differentiableAt_pi.2 fun _ => ?_
    exact differentiableAt_line_of_shift (u := fun z => ∫ ω, g z ω ∂μ)
      (hline _ hζ j).2.differentiableAt
end ComplexAnalysis
end YangMills.Construction
