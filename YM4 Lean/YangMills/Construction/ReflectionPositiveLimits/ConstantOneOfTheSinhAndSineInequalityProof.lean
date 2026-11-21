import YangMills.Construction.ReflectionPositiveLimits.ConstantOneOfTheSinhAndSineInequality
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositiveLimits.SinhSineInequality
theorem sinh_half_chain {E q t : ℝ} (hEq : E ≥ |q|) (htpos : 0 < t) :
    Real.sinh (t * E / 2) ≥ t * E / 2 ∧ t * E / 2 ≥ t * |q| / 2 ∧
      t * |q| / 2 ≥ |Real.sin (t * q / 2)| := by
  have hE : 0 ≤ E := le_trans (abs_nonneg q) hEq
  refine ⟨Real.self_le_sinh_iff.2 (by positivity), ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hEq htpos.le
    linarith
  · calc |Real.sin (t * q / 2)| ≤ |t * q / 2| := Real.abs_sin_le_abs
      _ = t * |q| / 2 := by
        rw [abs_div, abs_mul, abs_of_pos htpos, abs_of_pos (two_pos : (0 : ℝ) < 2)]
theorem ge_abs_of_accPt_of_sinhDominates {E q : ℝ} {S : Set ℝ} (hS : S ⊆ Set.Ioi 0)
    (hacc : AccPt (0 : ℝ) (𝓟 S))
    (hdom : ∀ t ∈ S, SinhDominatesAbsSin E q t) : E ≥ |q| := by
  have hlin : ∀ c : ℝ, HasDerivAt (fun t : ℝ => t * c / 2) (c / 2) 0 := fun c => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).div_const 2
  have hsinh : HasDerivAt (fun t : ℝ => Real.sinh (t * E / 2)) (E / 2) 0 := by
    simpa using (hlin E).sinh
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (t * q / 2)) (q / 2) 0 := by
    simpa using (hlin q).sin
  have tsinh : Tendsto (fun t : ℝ => t⁻¹ * Real.sinh (t * E / 2)) (𝓝[≠] 0) (𝓝 (E / 2)) := by
    simpa using hsinh.tendsto_slope_zero
  have tsin : Tendsto (fun t : ℝ => t⁻¹ * Real.sin (t * q / 2)) (𝓝[≠] 0) (𝓝 (q / 2)) := by
    simpa using hsin.tendsto_slope_zero
  have : NeBot (𝓝[≠] (0 : ℝ) ⊓ 𝓟 S) := hacc
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ) ⊓ 𝓟 S,
      |t⁻¹ * Real.sin (t * q / 2)| ≤ t⁻¹ * Real.sinh (t * E / 2) := by
    filter_upwards [mem_inf_of_right (mem_principal_self S)] with t ht
    have tpos : 0 < t := hS ht
    have hb : |Real.sin (t * q / 2)| ≤ Real.sinh (t * E / 2) := hdom t ht
    rw [abs_mul, abs_of_pos (inv_pos.2 tpos)]
    exact mul_le_mul_of_nonneg_left hb (inv_pos.2 tpos).le
  have hle := le_of_tendsto_of_tendsto ((tsin.mono_left inf_le_left).abs)
    (tsinh.mono_left inf_le_left) hev
  rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)] at hle
  linarith
theorem accPt_zero_posAdicGridPoints {L : ℕ} (hL : 2 ≤ L) :
    AccPt (0 : ℝ) (𝓟 (ReflectionPositivity.posAdicGridPoints L)) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hpos : ∀ k : ℕ, 0 < ((L : ℝ)⁻¹) ^ k := fun k => pow_pos (inv_pos.2 hL0) k
  have hlim0 : Tendsto (fun k : ℕ => ((L : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.2 hL0).le (inv_lt_one_of_one_lt₀ hL1)
  have hmem : ∀ k : ℕ, ((L : ℝ)⁻¹) ^ k ∈ ReflectionPositivity.posAdicGridPoints L := fun k =>
    ⟨(PeriodicLattice.mem_adicGridPoints_iff L _).2 ⟨k, 1, by simp [PeriodicLattice.meshSize]⟩,
      hpos k⟩
  have hlim : Tendsto (fun k : ℕ => ((L : ℝ)⁻¹) ^ k) atTop
      (𝓝[≠] (0 : ℝ) ⊓ 𝓟 (ReflectionPositivity.posAdicGridPoints L)) :=
    tendsto_inf.2 ⟨tendsto_nhdsWithin_iff.2 ⟨hlim0, Eventually.of_forall fun k => (hpos k).ne'⟩,
      tendsto_principal.2 (Eventually.of_forall hmem)⟩
  exact hlim.neBot
theorem sinhDominatesAbsSinIffStatement_holds : SinhDominatesAbsSinIffStatement := by
  intro L hL E q _
  refine ⟨⟨fun hdom => ?_, fun hEq t ht => ?_⟩,
    fun S hS hacc hdom => ge_abs_of_accPt_of_sinhDominates hS hacc hdom,
    fun hEq t ht => sinh_half_chain hEq ht⟩
  · exact ge_abs_of_accPt_of_sinhDominates (fun t ht => ht.2)
      (accPt_zero_posAdicGridPoints (le_trans (by norm_num) hL.2)) hdom
  · have ht0 : 0 < t := ht.2
    obtain ⟨h1, h2, h3⟩ := sinh_half_chain hEq ht0
    exact le_trans h3 (le_trans h2 h1)
end YangMills.Construction.ReflectionPositiveLimits.SinhSineInequality
