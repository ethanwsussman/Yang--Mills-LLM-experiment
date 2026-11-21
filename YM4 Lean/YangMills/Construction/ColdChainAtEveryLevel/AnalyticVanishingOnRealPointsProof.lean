import YangMills.Construction.ColdChainAtEveryLevel.AnalyticVanishingOnRealPoints
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace YangMills.Construction.Analytic
variable {k : ℕ}
theorem sum_norm_update (z : Fin k → ℂ) (j : Fin k) (w : ℂ) :
    ∑ l, ‖Function.update z j w l‖ = ∑ l, ‖z l‖ - ‖z j‖ + ‖w‖ := by
  classical
  have h : ∀ l, ‖Function.update z j w l‖ = ‖z l‖ + (if l = j then ‖w‖ - ‖z j‖ else 0) := by
    intro l
    by_cases hl : l = j
    · subst hl
      simp
    · simp [hl]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
theorem vanishingOnRealPoints : vanishingOnRealPointsStatement := by
  intro k r g hg hreal
  classical
  have key : ∀ u : Finset (Fin k), ∀ z : Fin k → ℂ, ∑ l, ‖z l‖ < r → (∀ l, l ∉ u → (z l).im = 0) → g z = 0 := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
      intro z hz him
      have e : z = fun l => (((z l).re : ℝ) : ℂ) := by
        funext l
        apply Complex.ext
        · simp
        · simpa using him l (by simp)
      rw [e]
      refine hreal _ (lt_of_le_of_lt (Finset.sum_le_sum fun l _ => ?_) hz)
      exact Complex.abs_re_le_norm _
    | insert j u hj ih =>
      intro z hz him
      set ρ := r - (∑ l, ‖z l‖ - ‖z j‖) with hρ
      have hρz : ‖z j‖ < ρ := by
        rw [hρ]
        linarith
      have hρpos : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hρz
      set φ : ℂ → ℂ := fun w => g (Function.update z j w) with hφ
      have hmem : ∀ w : ℂ, ‖w‖ < ρ → ∑ l, ‖Function.update z j w l‖ < r := by
        intro w hw
        rw [sum_norm_update]
        rw [hρ] at hw
        linarith
      have hline : ∀ w₀ : ℂ, AnalyticAt ℂ (fun w : ℂ => Function.update z j w) w₀ := by
        intro w₀
        rw [analyticAt_pi_iff]
        intro l
        by_cases hl : l = j
        · subst hl
          have e : (fun w : ℂ => Function.update z l w l) = fun w => w := by
            funext w
            simp
          rw [e]
          exact analyticAt_id
        · have e : (fun w : ℂ => Function.update z j w l) = fun _ => z l := by
            funext w
            simp [hl]
          rw [e]
          exact analyticAt_const
      have hφa : AnalyticOnNhd ℂ φ (Metric.ball 0 ρ) := by
        intro w hw
        have hw' : ‖w‖ < ρ := by simpa using hw
        exact AnalyticAt.comp (g := g) (hg _ (hmem w hw')) (hline w)
      have hφreal : ∀ t : ℝ, |t| < ρ → φ (t : ℂ) = 0 := by
        intro t ht
        refine ih _ (hmem _ (by simpa [Complex.norm_real] using ht)) fun l hl => ?_
        by_cases hlj : l = j
        · subst hlj
          simp
        · have : l ∉ insert j u := by
            simp [hlj, hl]
          simpa [hlj] using him l this
      have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), φ w = 0 := by
        have hseq : Tendsto (fun n : ℕ => (((ρ / ((n : ℝ) + 2) : ℝ)) : ℂ)) atTop (𝓝[≠] 0) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
          · have h1 : Tendsto (fun n : ℕ => ρ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
              Tendsto.div_atTop tendsto_const_nhds
                (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
            have h3 : Tendsto (fun n : ℕ => (((ρ / ((n : ℝ) + 2) : ℝ)) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
              (Complex.continuous_ofReal.tendsto 0).comp h1
            simpa only [Complex.ofReal_zero] using h3
          · have : ρ / ((n : ℝ) + 2) ≠ 0 := by positivity
            exact Complex.ofReal_ne_zero.2 this
        refine hseq.frequently (Frequently.of_forall fun n => hφreal _ ?_)
        have hp : 0 < ρ / ((n : ℝ) + 2) := by positivity
        rw [abs_of_pos hp]
        have h2 : (1 : ℝ) < (n : ℝ) + 2 := by
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        exact div_lt_self hρpos h2
      have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by simpa using hρpos
      have heq := hφa.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (convex_ball (0 : ℂ) ρ).isPreconnected h0 hfreq
      have hzj : z j ∈ Metric.ball (0 : ℂ) ρ := by simpa using hρz
      have := heq hzj
      simpa [hφ] using this
  intro z hz
  exact key Finset.univ z hz (fun l hl => absurd (Finset.mem_univ l) hl)
end YangMills.Construction.Analytic
end
