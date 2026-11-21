import YangMills.Construction.ResponseInTheExpansion.TailOfAScore
import YangMills.Construction.SummableBoundsOfTheFlow.GroupGapHasItsTail
import YangMills.Construction.SummableBoundsOfTheFlow.TheTailOfTheGapIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace YangMills.Construction.WeightedResponses
private def dilatedPow (t : ℝ) (g : ℝ → ℝ) (m : ℕ) (r : ℝ) : ℝ := g (t / r) * (r ^ m)⁻¹
private def dilationStep (g : ℝ → ℝ) (m : ℕ) (u : ℝ) : ℝ := -(u * deriv g u + m * g u)
private theorem dilationStep_contDiffOn {U : Set ℝ} (hU : IsOpen U) {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g U) (m : ℕ) :
    ContDiffOn ℝ ∞ (dilationStep g m) U := by
  have hd : ContDiffOn ℝ ∞ (deriv g) U := hg.deriv_of_isOpen hU (by simp)
  unfold dilationStep
  exact ((contDiffOn_id.mul hd).add (contDiffOn_const.mul hg)).neg
private theorem hasDerivAt_inv_pow {r : ℝ} (hr : 0 < r) (m : ℕ) :
    HasDerivAt (fun y : ℝ => (y ^ m)⁻¹) (-(m : ℝ) * (r ^ (m + 1))⁻¹) r := by
  cases m with
  | zero => simpa using hasDerivAt_const r (1 : ℝ)
  | succ n =>
    have h := (hasDerivAt_pow (n + 1) r).inv (pow_ne_zero _ hr.ne')
    have e : -(((n + 1 : ℕ) : ℝ) * r ^ (n + 1 - 1)) / (r ^ (n + 1)) ^ 2 =
        -((n + 1 : ℕ) : ℝ) * (r ^ (n + 1 + 1))⁻¹ := by
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
    rw [← e]
    exact h
private theorem dilatedPow_hasDerivAt {U : Set ℝ} (hU : IsOpen U) {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g U) {t r : ℝ}
    (m : ℕ) (hr : 0 < r) (hu : t / r ∈ U) :
    HasDerivAt (dilatedPow t g m) (dilatedPow t (dilationStep g m) (m + 1) r) r := by
  have hd : HasDerivAt g (deriv g (t / r)) (t / r) :=
    ((hg.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hu)).hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => t / y) (-t * (r ^ 2)⁻¹) r := by
    have := (hasDerivAt_inv hr.ne').const_mul t
    simpa [div_eq_mul_inv] using this
  have h2 := (hd.comp r h1).mul (hasDerivAt_inv_pow hr m)
  have e : dilatedPow t (dilationStep g m) (m + 1) r =
      deriv g (t / r) * (-t * (r ^ 2)⁻¹) * (r ^ m)⁻¹ + g (t / r) * (-(m : ℝ) * (r ^ (m + 1))⁻¹) := by
    have hr' := hr.ne'
    unfold dilatedPow dilationStep
    field_simp
    ring
  rw [e]
  exact h2
private theorem dilatedPow_contDiffOn {U : Set ℝ} {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hsub : Icc (0 : ℝ) 1 ⊆ U) {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) (m : ℕ) (n : ℕ∞) :
    ContDiffOn ℝ n (dilatedPow t g m) (Icc (1 / 2) 1) := by
  have hne : ∀ r ∈ Icc (1 / 2 : ℝ) 1, r ≠ 0 := fun r hr => by
    have := hr.1
    intro h
    rw [h] at this
    norm_num at this
  have hdiv : ContDiffOn ℝ n (fun r : ℝ => t / r) (Icc (1 / 2) 1) := contDiffOn_const.div contDiffOn_id hne
  have hmap : MapsTo (fun r : ℝ => t / r) (Icc (1 / 2) 1) U := fun r hr => hsub (by
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
    exact ⟨by positivity, (div_le_one hr0).2 (ht2.trans hr.1)⟩)
  have hg' : ContDiffOn ℝ n g U := hg.of_le (by exact_mod_cast le_top)
  have hinv : ContDiffOn ℝ n (fun r : ℝ => (r ^ m)⁻¹) (Icc (1 / 2) 1) :=
    (contDiffOn_id.pow m).inv (fun r hr => pow_ne_zero _ (hne r hr))
  exact (hg'.comp hdiv hmap).mul hinv
private theorem dilatedPow_iteratedDerivWithin_bound {U : Set ℝ} (hU : IsOpen U) (hsub : Icc (0 : ℝ) 1 ⊆ U)
    (k : ℕ) :
    ∀ (g : ℝ → ℝ) (m : ℕ), ContDiffOn ℝ ∞ g U → ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      ∀ r ∈ Icc (1 / 2 : ℝ) 1, |iteratedDerivWithin k (dilatedPow t g m) (Icc (1 / 2) 1) r| ≤ C := by
  induction k with
  | zero =>
    intro g m hg
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn.mono hsub)
    refine ⟨|C| * 2 ^ m, fun t ht ht2 r hr => ?_⟩
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
    have hu : t / r ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hr0).2 (ht2.trans hr.1)⟩
    have h1 : |g (t / r)| ≤ |C| := (by simpa using hC _ hu : |g (t / r)| ≤ C).trans (le_abs_self C)
    have h2 : |(r ^ m)⁻¹| ≤ 2 ^ m := by
      have hh : (1 / 2 : ℝ) ^ m ≤ r ^ m := pow_le_pow_left₀ (by norm_num) hr.1 m
      rw [abs_of_pos (by positivity)]
      calc (r ^ m)⁻¹ ≤ ((1 / 2 : ℝ) ^ m)⁻¹ := inv_anti₀ (by positivity) hh
        _ = 2 ^ m := by simp
    rw [iteratedDerivWithin_zero]
    unfold dilatedPow
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
  | succ k ih =>
    intro g m hg
    obtain ⟨C, hC⟩ := ih (dilationStep g m) (m + 1) (dilationStep_contDiffOn hU hg m)
    refine ⟨C, fun t ht ht2 r hr => ?_⟩
    have heq : EqOn (derivWithin (dilatedPow t g m) (Icc (1 / 2) 1)) (dilatedPow t (dilationStep g m) (m + 1))
        (Icc (1 / 2) 1) := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
      have hu : t / y ∈ U := hsub ⟨by positivity, (div_le_one hy0).2 (ht2.trans hy.1)⟩
      exact (dilatedPow_hasDerivAt hU hg m hy0 hu).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc (by norm_num) y hy)
    rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr heq hr]
    exact hC t ht ht2 r hr
theorem scoreRemainderExpansion_of_haarGap (hG : ScaledVariables.HaarGapLogTail)
    (hS : ScaledVariables.HaarGapTailSmooth) : ScoreRemainderExpansion := by
  obtain ⟨h, hsm, hpos, hlog⟩ := hS
  have hUo : IsOpen {u : ℝ | h u ≠ 0} := isOpen_ne_fun hsm.continuous continuous_const
  have hsub : Icc (0 : ℝ) 1 ⊆ {u : ℝ | h u ≠ 0} := fun u hu => (hpos u hu.1).ne'
  have hGs : ContDiffOn ℝ ∞ (fun u => -Real.log (h u)) {u : ℝ | h u ≠ 0} :=
    (hsm.contDiffOn.log (fun u hu => hu)).neg
  have hev : ∀ u : ℝ, 0 < u → ScaledVariables.haarGapTail =ᶠ[𝓝 u] fun u => -Real.log (h u) := fun u hu => by
    filter_upwards [lt_mem_nhds hu] with y hy
    exact hlog y hy.le
  have hderiv : ∀ u : ℝ, 0 < u →
      deriv ScaledVariables.haarGapTail u = deriv (fun u => -Real.log (h u)) u :=
    fun u hu => (hev u hu).deriv_eq
  have hdiff : ∀ u : ℝ, 0 < u → DifferentiableAt ℝ ScaledVariables.haarGapTail u := fun u hu => by
    have hin : u ∈ {u : ℝ | h u ≠ 0} := (hpos u hu.le).ne'
    exact ((hGs.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds hin)).congr_of_eventuallyEq (hev u hu)
  refine ⟨fun Q r h1 hr => ?_, fun a ha k => ?_⟩
  · have hax : 0 < Q.a * Q.coupling := by
      by_contra hn
      have : Q.a * Q.coupling * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hr.le
      linarith
    have hs : 0 < Q.a * Q.coupling * r := mul_pos hax hr
    set s := Q.a * Q.coupling * r with hs_def
    have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(s ^ 2)⁻¹) s := by
      simpa only [one_div] using hasDerivAt_inv hs.ne'
    have hT : HasDerivAt (fun y : ℝ => ScaledVariables.haarGapTail (1 / y))
        (deriv ScaledVariables.haarGapTail (1 / s) * -(s ^ 2)⁻¹) s :=
      (hdiff (1 / s) (by positivity)).hasDerivAt.comp s hinv
    have hL : HasDerivAt (fun y : ℝ => 3 / 2 * Real.log y) (3 / 2 * s⁻¹) s :=
      (Real.hasDerivAt_log hs.ne').const_mul _
    have hA : HasDerivAt (fun y : ℝ => 3 / 2 * Real.log y + ScaledVariables.haarGapTail (1 / y))
        (3 / 2 * s⁻¹ + deriv ScaledVariables.haarGapTail (1 / s) * -(s ^ 2)⁻¹) s := hL.add hT
    have hE : ColdStepAtMirrorFrames.haarGap =ᶠ[𝓝 s]
        fun y : ℝ => 3 / 2 * Real.log y + ScaledVariables.haarGapTail (1 / y) := by
      filter_upwards [lt_mem_nhds hs] with y hy
      exact hG y hy
    rw [(hA.congr_of_eventuallyEq hE).deriv]
    have ha0 : Q.a ≠ 0 := left_ne_zero_of_mul hax.ne'
    have hx0 : Q.coupling ≠ 0 := right_ne_zero_of_mul hax.ne'
    have hr0 := hr.ne'
    simp only [ColdHalfLaw.scoreRemainder]
    rw [hs_def]
    field_simp
  · obtain ⟨C, hC⟩ := dilatedPow_iteratedDerivWithin_bound hUo hsub k
      (fun u => -deriv (fun u => -Real.log (h u)) u / a ^ 2) 1
      ((hGs.deriv_of_isOpen hUo (by simp)).neg.div_const _)
    refine ⟨C, fun Q hQ hx => ?_⟩
    have ha0 : 0 < a := by linarith
    have hax : 2 ≤ a * Q.coupling := by
      have := mul_le_mul_of_nonneg_left hx ha0.le
      rwa [mul_div_cancel₀ _ ha0.ne'] at this
    have hax0 : 0 < a * Q.coupling := by linarith
    have ht : 0 < 1 / (a * Q.coupling) := by positivity
    have ht2 : 1 / (a * Q.coupling) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hax
    have heq : EqOn Q.scoreRemainder
        (dilatedPow (1 / (a * Q.coupling)) (fun u => -deriv (fun u => -Real.log (h u)) u / a ^ 2) 1)
        (Icc (1 / 2) 1) := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
      have e : 1 / (a * Q.coupling) / r = 1 / (a * Q.coupling * r) := by rw [div_div]
      simp only [ColdHalfLaw.scoreRemainder, dilatedPow, hQ, e]
      rw [hderiv _ (by positivity)]
      field_simp
    refine ⟨(dilatedPow_contDiffOn ((hGs.deriv_of_isOpen hUo (by simp)).neg.div_const _) hsub ht ht2 1 k).congr heq,
      fun r hr => ?_⟩
    rw [iteratedDerivWithin_congr heq hr]
    exact hC _ ht ht2 r hr
end YangMills.Construction.WeightedResponses
end
