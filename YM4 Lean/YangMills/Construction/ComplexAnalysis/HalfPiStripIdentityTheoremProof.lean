import YangMills.Construction.ComplexAnalysis.HalfPiStripIdentityTheorem
import Mathlib
set_option autoImplicit false
open Filter Topology
namespace YangMills.Construction.Strips
theorem eqOnHalfPiStripOfEqOnReal : EqOnHalfPiStripOfEqOnReal := by
  intro f g hf hg hfg
  have hopen : IsOpen halfPiStrip :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hconv : Convex ℝ halfPiStrip := by
    have hset : halfPiStrip =
        {c : ℂ | -(Real.pi / 2) < c.im} ∩ {c : ℂ | c.im < Real.pi / 2} := by
      ext ζ
      simp [halfPiStrip, abs_lt]
    rw [hset]
    exact (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)
  have h0 : (0 : ℂ) ∈ halfPiStrip := by
    simp [halfPiStrip, Real.pi_pos]
  have hlim : Tendsto (fun k : ℕ => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have hreal : Tendsto (fun k : ℕ => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop
          (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [Complex.ofReal_zero] at hreal
    · exact Set.mem_compl_singleton_iff.2 (Complex.ofReal_ne_zero.2 (by positivity))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z :=
    hlim.frequently (Frequently.of_forall fun k => hfg _)
  exact (hf.analyticOnNhd hopen).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hopen)
    hconv.isPreconnected h0 hfreq
end YangMills.Construction.Strips
