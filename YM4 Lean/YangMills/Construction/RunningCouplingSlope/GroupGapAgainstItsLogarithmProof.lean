import YangMills.Construction.RunningCouplingSlope.GroupGapAgainstItsLogarithm
import YangMills.Construction.SummableBoundsOfTheFlow.GroupGapHasItsTail
import YangMills.Construction.SummableBoundsOfTheFlow.TheTailOfTheGapIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace YangMills.Construction.RunningCouplingSlope
theorem haarGapSubLog_deriv_bounds (hTail : ScaledVariables.HaarGapLogTail)
    (hSmooth : ScaledVariables.HaarGapTailSmooth) : HaarGapSubLogDerivBounds := by
  obtain ⟨h, hsm, hpos, hlog⟩ := hSmooth
  obtain ⟨U, hU⟩ : ∃ U : Set ℝ, U = {u : ℝ | h u ≠ 0} := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun u => -Real.log (h u) := ⟨_, rfl⟩
  have hUo : IsOpen U := hU ▸ isOpen_ne_fun hsm.continuous continuous_const
  have hgs : ContDiffOn ℝ ∞ g U := by
    rw [hg]
    exact (hsm.contDiffOn.log (fun u hu => by rw [hU] at hu; exact hu)).neg
  have hd1 : ContDiffOn ℝ ∞ (deriv g) U := hgs.deriv_of_isOpen hUo (by simp)
  have hd2 : ContDiffOn ℝ ∞ (deriv (deriv g)) U := hd1.deriv_of_isOpen hUo (by simp)
  have hnn : ∀ u : ℝ, 0 ≤ u → u ∈ U := fun u hu => by
    rw [hU]
    exact (hpos u hu).ne'
  have hsub : Icc (0 : ℝ) 1 ⊆ U := fun u hu => hnn u hu.1
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hd1.continuousOn.mono hsub)
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn (hd2.continuousOn.mono hsub)
  have heq : ∀ s : ℝ, 0 < s → LaplaceAsymptotics.haarGapSubLog s = g s⁻¹ := fun s hs => by
    have h1 := hTail s hs
    have h2 := hlog (1 / s) (by positivity)
    unfold LaplaceAsymptotics.haarGapSubLog
    rw [h1, h2, hg]
    simp
  have hinv : ∀ s : ℝ, 0 < s → HasDerivAt (fun y : ℝ => y⁻¹) (-(s ^ 2)⁻¹) s := fun s hs =>
    hasDerivAt_inv hs.ne'
  have hgd : ∀ u ∈ U, HasDerivAt g (deriv g u) u := fun u hu =>
    ((hgs.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds hu)).hasDerivAt
  have hgd' : ∀ u ∈ U, HasDerivAt (deriv g) (deriv (deriv g) u) u := fun u hu =>
    ((hd1.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds hu)).hasDerivAt
  have hfirst : ∀ s : ℝ, 0 < s →
      deriv LaplaceAsymptotics.haarGapSubLog s = deriv g s⁻¹ * -(s ^ 2)⁻¹ := fun s hs => by
    have hcomp : HasDerivAt (fun y : ℝ => g y⁻¹) (deriv g s⁻¹ * -(s ^ 2)⁻¹) s :=
      HasDerivAt.comp s (hgd s⁻¹ (hnn _ (by positivity))) (hinv s hs)
    have hev : LaplaceAsymptotics.haarGapSubLog =ᶠ[𝓝 s] fun y : ℝ => g y⁻¹ := by
      filter_upwards [Ioi_mem_nhds hs] with y hy
      exact heq y hy
    exact (hcomp.congr_of_eventuallyEq hev).deriv
  have hsecond : ∀ s : ℝ, 0 < s → iteratedDeriv 2 LaplaceAsymptotics.haarGapSubLog s =
      deriv (deriv g) s⁻¹ * -(s ^ 2)⁻¹ * -(s ^ 2)⁻¹ + deriv g s⁻¹ * (2 * (s ^ 3)⁻¹) :=
      fun s hs => by
    have hc : HasDerivAt (fun y : ℝ => deriv g y⁻¹) (deriv (deriv g) s⁻¹ * -(s ^ 2)⁻¹) s :=
      HasDerivAt.comp s (hgd' s⁻¹ (hnn _ (by positivity))) (hinv s hs)
    have hq : HasDerivAt (fun y : ℝ => -(y ^ 2)⁻¹) (2 * (s ^ 3)⁻¹) s := by
      have h0 := ((hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs.ne')).neg
      have e : -(-(((2 : ℕ) : ℝ) * s ^ (2 - 1)) / (s ^ 2) ^ 2) = 2 * (s ^ 3)⁻¹ := by
        have := hs.ne'
        simp only [Nat.add_one_sub_one, Nat.cast_ofNat, pow_one]
        field_simp
      rw [e] at h0
      exact h0
    have hprod := hc.mul hq
    have hev : deriv LaplaceAsymptotics.haarGapSubLog =ᶠ[𝓝 s]
        fun y : ℝ => deriv g y⁻¹ * -(y ^ 2)⁻¹ := by
      filter_upwards [Ioi_mem_nhds hs] with y hy
      exact hfirst y hy
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (hprod.congr_of_eventuallyEq hev).deriv
  refine ⟨2 * |C1| + |C2| + 1, by positivity, fun s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  have hu : s⁻¹ ∈ Icc (0 : ℝ) 1 := ⟨by positivity, inv_le_one_of_one_le₀ hs⟩
  have b1 : |deriv g s⁻¹| ≤ |C1| :=
    (by simpa using hC1 _ hu : |deriv g s⁻¹| ≤ C1).trans (le_abs_self C1)
  have b2 : |deriv (deriv g) s⁻¹| ≤ |C2| :=
    (by simpa using hC2 _ hu : |deriv (deriv g) s⁻¹| ≤ C2).trans (le_abs_self C2)
  have hC : 0 ≤ |C1| := abs_nonneg _
  have hC' : 0 ≤ |C2| := abs_nonneg _
  constructor
  · rw [hfirst s hs0]
    have e : s * (deriv g s⁻¹ * -(s ^ 2)⁻¹) = -deriv g s⁻¹ / s := by
      field_simp
    rw [e, abs_div, abs_neg, abs_of_pos hs0]
    exact div_le_div_of_nonneg_right (by linarith) hs0.le
  · rw [hsecond s hs0]
    have e : s ^ 2 * (deriv (deriv g) s⁻¹ * -(s ^ 2)⁻¹ * -(s ^ 2)⁻¹ +
        deriv g s⁻¹ * (2 * (s ^ 3)⁻¹)) =
        (deriv (deriv g) s⁻¹ * s⁻¹ + 2 * deriv g s⁻¹) / s := by
      field_simp
    rw [e, abs_div, abs_of_pos hs0]
    refine div_le_div_of_nonneg_right ?_ hs0.le
    have hi : |s⁻¹| ≤ 1 := by
      rw [abs_of_nonneg hu.1]
      exact hu.2
    calc |deriv (deriv g) s⁻¹ * s⁻¹ + 2 * deriv g s⁻¹|
        ≤ |deriv (deriv g) s⁻¹ * s⁻¹| + |2 * deriv g s⁻¹| := abs_add_le _ _
      _ ≤ |C2| * 1 + 2 * |C1| := by
        rw [abs_mul, abs_mul, abs_two]
        have := mul_le_mul b2 hi (abs_nonneg _) hC'
        linarith
      _ ≤ 2 * |C1| + |C2| + 1 := by linarith
end YangMills.Construction.RunningCouplingSlope
end
