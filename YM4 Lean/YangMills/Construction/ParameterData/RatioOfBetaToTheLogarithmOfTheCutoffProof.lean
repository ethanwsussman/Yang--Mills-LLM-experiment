import YangMills.Construction.ParameterData.FirstPassageOfTheFlow
import YangMills.Construction.ParameterData.RatioOfBetaToTheLogarithmOfTheCutoff
import YangMills.Construction.ParameterData.TheCouplingAlongTheLine
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
open Filter Topology
private lemma tendsto_log_one_add_mul_div {b : ℝ} (hb : 0 < b) :
    Tendsto (fun K : ℕ => Real.log (1 + b * K) / K) atTop (𝓝 0) := by
  have hu : Tendsto (fun K : ℕ => 1 + b * (K : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop hb)
  have h := (Real.tendsto_pow_log_div_mul_add_atTop (1 / b) (-(1 / b)) 1
    (one_div_ne_zero hb.ne')).comp hu
  refine h.congr fun K => ?_
  have hK : 1 / b * (1 + b * (K : ℝ)) + -(1 / b) = K := by
    field_simp
    ring
  simp only [Function.comp, pow_one, hK]
abbrev _root_.YangMills.SharedProofs.p26208 := @tendsto_log_one_add_mul_div
private lemma tendsto_ratioError {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y)
    (hc : 0 < D.c₀) (hX : 0 < D.X₀) (g : ℝ) : Tendsto (D.ratioError g) atTop (𝓝 0) := by
  have hb : 0 < 3 * D.c₀ / (4 * D.X₀) := by positivity
  have h1 : Tendsto (fun K : ℕ => ((K : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have h2 := tendsto_log_one_add_mul_div hb
  have h3 := (h1.const_mul ((D.threshold g + 2 * D.cH + D.Cr) / Real.log T.side)).add
    (h2.const_mul (8 * D.Md / (3 * D.c₀) / Real.log T.side))
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun K => ?_
  have hm : 3 * D.c₀ * (K : ℝ) / (4 * D.X₀) = 3 * D.c₀ / (4 * D.X₀) * K := by ring
  simp only [TrajectoryParameters.ratioError, TrajectoryParameters.lineGap, hm]
  ring
private lemma firstPassageIndex_unique {B g : ℝ} {x : ℕ → ℝ} {K K' : ℕ}
    (h : SequencePassage.IsFirstPassageIndex B g x K)
    (h' : SequencePassage.IsFirstPassageIndex B g x K') : K = K' := by
  rcases lt_trichotomy K K' with hlt | heq | hlt
  · exact absurd h.1 (not_le.mpr (h'.2 K hlt))
  · exact heq
  · exact absurd h'.1 (not_le.mpr (h.2 K' hlt))
abbrev _root_.YangMills.SharedProofs.p54782 := @firstPassageIndex_unique
theorem betaLogCutoffRatio (hLine : couplingAlongLineStatement)
    (hPass : firstPassageExistsStatement) : betaLogCutoffRatioStatement := by
  intro T y D hD g hg hy
  have hslope : 10 < D.c₀ := hD.errorMargin.slope_gt
  have hc : 0 < D.c₀ := by linarith
  have hX : 0 < D.X₀ := by linarith [hD.errorMargin.floor_ge]
  have hc₀ : D.c₀ = logSlope * Real.log T.side := rfl
  have hs : 0 < logSlope := by
    unfold logSlope
    positivity
  have hl : 0 < Real.log T.side := by
    by_contra hn
    have : logSlope * Real.log T.side ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs.le (not_lt.mp hn)
    linarith
  refine ⟨tendsto_ratioError D hc hX g, fun K β hK hβ => ?_⟩
  obtain ⟨hβtop, hcut⟩ := hβ
  obtain ⟨K', hpass⟩ := hPass T y D hD g hg hy β hβtop
  have hKK : K' = K := firstPassageIndex_unique hpass.isFirstPassageIndex hcut
  subst hKK
  have hline := hLine T y D hD g hg hy K' β ⟨hβtop, hcut⟩ 0 (Nat.zero_le _)
  have hx0 : D.coupling β 0 = β := rfl
  rw [hx0, Nat.sub_zero] at hline
  have hxpos : 0 < D.coupling β K' := lt_trans (zpow_pos hg _) (hpass.coupling_gt K' le_rfl)
  have hxtop : D.coupling β K' ≤ D.threshold g := hcut.1
  have hKpos : (0 : ℝ) < K' := by exact_mod_cast hK
  have hlog : Real.log (1 / (T.side : ℝ) ^ (-(K' : ℤ))) = K' * Real.log T.side := by
    rw [zpow_neg, one_div, inv_inv, zpow_natCast, Real.log_pow]
  have hden : 0 < (K' : ℝ) * Real.log T.side := mul_pos hKpos hl
  rw [hlog]
  have hsub : β / ((K' : ℝ) * Real.log T.side) - logSlope =
      (β - D.c₀ * K') / ((K' : ℝ) * Real.log T.side) := by
    rw [hc₀]
    field_simp
  rw [hsub, abs_div, abs_of_pos hden, TrajectoryParameters.ratioError]
  refine div_le_div_of_nonneg_right ?_ hden.le
  have hb := abs_le.mp hline
  rw [Nat.cast_zero, sub_zero] at hb
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [hb.1, hb.2]
end YangMills.Construction.TrajectoryData
end
