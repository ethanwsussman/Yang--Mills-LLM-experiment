import YangMills.Construction.ClusterExpansionOfAStep.DerivativesUnderAnIntegral
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction.ParametricIntegral
variable {α : Type} [MeasurableSpace α] {μ : Measure α} {k : ℕ}
theorem aestronglyMeasurable_fderiv_of_forall {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set (Fin k → ℝ)} (hU : IsOpen U) {F : α → (Fin k → ℝ) → G} {x : Fin k → ℝ} (hx : x ∈ U)
    (hdiff : ∀ a, DifferentiableAt ℝ (F a) x)
    (hmeas : ∀ y ∈ U, AEStronglyMeasurable (fun a => F a y) μ) :
    AEStronglyMeasurable (fun a => fderiv ℝ (F a) x) μ := by
  classical
  have hdir : ∀ e : Fin k → ℝ, AEStronglyMeasurable (fun a => fderiv ℝ (F a) x e) μ := by
    intro e
    have hline : ContinuousAt (fun s : ℝ => x + s • e) 0 := by fun_prop
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • e ∈ U :=
      hline.eventually (by simpa using hU.mem_nhds hx)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    let t : ℕ → ℝ := fun m => ε / 2 / (m + 1)
    have ht0 : ∀ m, 0 < t m := fun m => by positivity
    have htlt : ∀ m, |t m| < ε := by
      intro m
      rw [abs_of_pos (ht0 m)]
      have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      calc t m ≤ ε / 2 := div_le_self (by positivity) h1
        _ < ε := by linarith
    have httend : Tendsto t atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m => (ht0 m).ne'⟩
      simpa [t] using tendsto_const_div_atTop_nhds_zero_nat (ε / 2) |>.comp (tendsto_add_atTop_nat 1) |>.congr
        (fun m => by simp)
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun m a => (t m)⁻¹ • (F a (x + t m • e) - F a x)) ?_ ?_
    · intro m
      have h1 : x + t m • e ∈ U := hball (by simpa [Real.dist_eq] using htlt m)
      exact ((hmeas _ h1).sub (hmeas _ hx)).const_smul _
    · refine Eventually.of_forall fun a => ?_
      have hder : HasDerivAt (fun s : ℝ => F a (x + s • e)) (fderiv ℝ (F a) x e) 0 := by
        have h1 : HasFDerivAt (F a) (fderiv ℝ (F a) x) (x + (0 : ℝ) • e) := by
          simpa using (hdiff a).hasFDerivAt
        have h2 : HasDerivAt (fun s : ℝ => x + s • e) e 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
        exact h1.comp_hasDerivAt (0 : ℝ) h2
      have := hder.tendsto_slope_zero.comp httend
      simpa [Function.comp_def] using this
  have hsum : (fun a => fderiv ℝ (F a) x) = fun a => ∑ i : Fin k,
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight
        (fderiv ℝ (F a) x (Pi.single i 1)) := by
    funext a
    ext v
    have hv : v = ∑ i : Fin k, v i • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum]
  rw [hsum]
  have hcont : ∀ i : Fin k, Continuous fun v : G =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight v :=
    fun i => (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) G
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i)).continuous
  have := Finset.aestronglyMeasurable_sum (f := fun (i : Fin k) a =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight
        (fderiv ℝ (F a) x (Pi.single i 1))) (μ := μ) Finset.univ
    (fun i _ => (hcont i).comp_aestronglyMeasurable (hdir _))
  convert this using 1
  funext a
  simp [Finset.sum_apply]
theorem contDiffOn_integral_and_norm_iteratedFDeriv_le (N : ℕ) :
    ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (U : Set (Fin k → ℝ)) (F : α → (Fin k → ℝ) → G) (g : α → ℝ), IsOpen U → Integrable g μ →
    (∀ a, ContDiffOn ℝ N (F a) U) → (∀ x ∈ U, AEStronglyMeasurable (fun a => F a x) μ) →
    (∀ a, ∀ j ≤ N, ∀ x ∈ U, ‖iteratedFDeriv ℝ j (F a) x‖ ≤ g a) →
    ContDiffOn ℝ N (fun x => ∫ a, F a x ∂μ) U ∧
      ∀ j ≤ N, ∀ x ∈ U, ∀ h : α → ℝ, Integrable h μ → (∀ a, ‖iteratedFDeriv ℝ j (F a) x‖ ≤ h a) →
        ‖iteratedFDeriv ℝ j (fun x => ∫ a, F a x ∂μ) x‖ ≤ ∫ a, h a ∂μ := by
  have hzero : ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (F : α → (Fin k → ℝ) → G) (x : Fin k → ℝ) (h : α → ℝ), Integrable h μ →
      (∀ a, ‖iteratedFDeriv ℝ 0 (F a) x‖ ≤ h a) →
      ‖iteratedFDeriv ℝ 0 (fun x => ∫ a, F a x ∂μ) x‖ ≤ ∫ a, h a ∂μ := by
    intro G _ _ _ F x h hh hb
    rw [norm_iteratedFDeriv_zero]
    refine norm_integral_le_of_norm_le hh (Eventually.of_forall fun a => ?_)
    simpa [norm_iteratedFDeriv_zero] using hb a
  induction N with
  | zero =>
    intro G _ _ _ U F g hU hg hF hm hb
    refine ⟨?_, ?_⟩
    · have hc : ContinuousOn (fun x => ∫ a, F a x ∂μ) U := by
        refine continuousOn_of_dominated (bound := g) ?_ ?_ hg ?_
        · intro x hx
          exact hm x hx
        · intro x hx
          refine Eventually.of_forall fun a => ?_
          simpa [norm_iteratedFDeriv_zero] using hb a 0 le_rfl x hx
        · refine Eventually.of_forall fun a => ?_
          simpa using (hF a).continuousOn
      simpa using hc
    · intro j hj x _ h hh hbd
      obtain rfl : j = 0 := by omega
      exact hzero G F x h hh hbd
  | succ N ih =>
    intro G _ _ _ U F g hU hg hF hm hb
    have hF1 : ∀ a, ContDiffOn ℝ ((N : WithTop ℕ∞) + 1) (F a) U := fun a => by
      simpa using hF a
    have hdiff : ∀ a, ∀ x ∈ U, DifferentiableAt ℝ (F a) x := fun a x hx =>
      ((hF1 a).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    have hF' : ∀ a, ContDiffOn ℝ N (fderiv ℝ (F a)) U := fun a =>
      (hF1 a).fderiv_of_isOpen hU le_rfl
    have hm' : ∀ x ∈ U, AEStronglyMeasurable (fun a => fderiv ℝ (F a) x) μ := by
      intro x hx
      exact aestronglyMeasurable_fderiv_of_forall hU hx (fun a => hdiff a x hx) hm
    have hb' : ∀ a, ∀ j ≤ N, ∀ x ∈ U, ‖iteratedFDeriv ℝ j (fderiv ℝ (F a)) x‖ ≤ g a := by
      intro a j hj x hx
      rw [norm_iteratedFDeriv_fderiv]
      exact hb a (j + 1) (by omega) x hx
    obtain ⟨h1, h2⟩ := ih ((Fin k → ℝ) →L[ℝ] G) U (fun a => fderiv ℝ (F a)) g hU hg hF' hm' hb'
    have hfd : ∀ x ∈ U, HasFDerivAt (fun x => ∫ a, F a x ∂μ) (∫ a, fderiv ℝ (F a) x ∂μ) x := by
      intro x hx
      refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x a => F a x)
        (F' := fun x a => fderiv ℝ (F a) x) (bound := g) (hU.mem_nhds hx) ?_ ?_ ?_ ?_ hg ?_)
      · exact Filter.eventually_of_mem (hU.mem_nhds hx) hm
      · refine hg.mono' (hm x hx) (Eventually.of_forall fun a => ?_)
        simpa [norm_iteratedFDeriv_zero] using hb a 0 (by omega) x hx
      · exact hm' x hx
      · refine Eventually.of_forall fun a y hy => ?_
        have := hb' a 0 (by omega) y hy
        simpa [norm_iteratedFDeriv_zero] using this
      · exact Eventually.of_forall fun a y hy => (hdiff a y hy).hasFDerivAt
    have hEq : Set.EqOn (fderiv ℝ (fun x => ∫ a, F a x ∂μ)) (fun x => ∫ a, fderiv ℝ (F a) x ∂μ) U :=
      fun x hx => (hfd x hx).fderiv
    refine ⟨?_, ?_⟩
    · have : ContDiffOn ℝ ((N : WithTop ℕ∞) + 1) (fun x => ∫ a, F a x ∂μ) U := by
        refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).mpr ⟨?_, by simp, ?_⟩
        · exact fun x hx => (hfd x hx).differentiableAt.differentiableWithinAt
        · exact h1.congr hEq
      simpa using this
    · intro j hj x hx h hh hbd
      rcases j with _ | j
      · exact hzero G F x h hh hbd
      · rw [← norm_iteratedFDeriv_fderiv]
        have hev : fderiv ℝ (fun x => ∫ a, F a x ∂μ) =ᶠ[𝓝 x] fun x => ∫ a, fderiv ℝ (F a) x ∂μ :=
          Filter.eventually_of_mem (hU.mem_nhds hx) hEq
        rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev j).eq_of_nhds]
        refine h2 j (by omega) x hx h hh fun a => ?_
        rw [norm_iteratedFDeriv_fderiv]
        exact hbd a
theorem contDiffOnIntegralStatement_holds : ContDiffOnIntegralStatement := by
  intro α _ μ k N U F g hU hg hF hm hb
  exact contDiffOn_integral_and_norm_iteratedFDeriv_le N ℝ U F g hU hg hF hm hb
end YangMills.Construction.ParametricIntegral
end
