import YangMills.Construction.Analysis.QuadraticTaylorUniqueness
import Mathlib
set_option autoImplicit false
open Filter Topology
namespace YangMills.Construction.Taylor
theorem quadraticTaylorUniqueness_holds : QuadraticTaylorUniqueness := by
  intro V _ _ φ β h
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hC
  have along_ray : ∀ (A : V) (s : ℝ), 0 < s → s * ‖A‖ < r →
      ‖φ A + (s : ℂ) * β A A‖ ≤ C * ‖A‖ ^ 3 * s ^ 2 := by
    intro A s hs hsr
    have hnorm : ‖(s : ℂ) • A‖ = s * ‖A‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have hmem : dist ((s : ℂ) • A) (0 : V) < r := by
      rwa [dist_zero_right, hnorm]
    have hb : ‖φ ((s : ℂ) • A) + β ((s : ℂ) • A) ((s : ℂ) • A)‖ ≤ C * ‖‖(s : ℂ) • A‖ ^ 3‖ :=
      hball hmem
    have hexp : φ ((s : ℂ) • A) + β ((s : ℂ) • A) ((s : ℂ) • A)
        = (s : ℂ) * (φ A + (s : ℂ) * β A A) := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hexp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le, hnorm, norm_pow,
      norm_mul, Real.norm_of_nonneg hs.le, norm_norm] at hb
    have hs' : s * ‖φ A + (s : ℂ) * β A A‖ ≤ s * (C * ‖A‖ ^ 3 * s ^ 2) :=
      hb.trans_eq (by ring)
    exact le_of_mul_le_mul_left hs' hs
  have eventually_small : ∀ A : V, ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧ s * ‖A‖ < r := by
    intro A
    have hc : Tendsto (fun s : ℝ => s * ‖A‖) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous fun s : ℝ => s * ‖A‖ := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact eventually_mem_nhdsWithin.and ((tendsto_order.1 hc).2 r hr)
  have hlin : ∀ A : V, φ A = 0 := by
    intro A
    have hleft : Tendsto (fun s : ℝ => ‖φ A + (s : ℂ) * β A A‖) (𝓝[>] 0) (𝓝 ‖φ A‖) := by
      have hcont : Continuous fun s : ℝ => ‖φ A + (s : ℂ) * β A A‖ := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hright : Tendsto (fun s : ℝ => C * ‖A‖ ^ 3 * s ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous fun s : ℝ => C * ‖A‖ ^ 3 * s ^ 2 := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hle : ‖φ A‖ ≤ 0 := le_of_tendsto_of_tendsto hleft hright
      ((eventually_small A).mono fun s hs => along_ray A s hs.1 hs.2)
    exact norm_le_zero_iff.1 hle
  refine ⟨LinearMap.ext hlin, fun A => ?_⟩
  have hstep : ∀ s : ℝ, 0 < s → s * ‖A‖ < r → ‖β A A‖ ≤ C * ‖A‖ ^ 3 * s := by
    intro s hs hsr
    have hb := along_ray A s hs hsr
    rw [hlin A, zero_add, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le] at hb
    have hs' : s * ‖β A A‖ ≤ s * (C * ‖A‖ ^ 3 * s) := hb.trans_eq (by ring)
    exact le_of_mul_le_mul_left hs' hs
  have hright : Tendsto (fun s : ℝ => C * ‖A‖ ^ 3 * s) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous fun s : ℝ => C * ‖A‖ ^ 3 * s := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : ‖β A A‖ ≤ 0 := ge_of_tendsto hright
    ((eventually_small A).mono fun s hs => hstep s hs.1 hs.2)
  exact norm_le_zero_iff.1 hle
end YangMills.Construction.Taylor
