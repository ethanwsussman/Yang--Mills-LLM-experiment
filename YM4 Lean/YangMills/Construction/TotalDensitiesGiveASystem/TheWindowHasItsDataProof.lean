import YangMills.Construction.ParameterData.RatioOfBetaToTheLogarithmOfTheCutoffProof
import YangMills.Construction.ParameterData.ScaleSequenceData
import YangMills.Construction.TotalDensitiesGiveASystem.TheWindowHasItsData
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open SystemsWithFiveBounds TrajectoryData
private theorem firstPassageIndex_unique {B g : ℝ} {x : ℕ → ℝ} {K K' : ℕ}
    (hK : SequencePassage.IsFirstPassageIndex B g x K)
    (hK' : SequencePassage.IsFirstPassageIndex B g x K') : K = K' := by apply _root_.YangMills.SharedProofs.p54782 <;> assumption
private theorem asymptoticFreedomSlope_eq_logSlope : asymptoticFreedomSlope = logSlope := by
  unfold asymptoticFreedomSlope logSlope
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  norm_num
theorem passageWindowData_of_trajectoryData (hD : trajectoryDataStatement) : passageWindowDataStatement := by
  obtain ⟨Q, hQ, sideFloor, rateCeiling, thresholdCeiling, n₀Floor, CsFloor, C₀, h1, h2, hT⟩ := hD
  refine ⟨⟨Q, sideFloor, fun _ => C₀, rateCeiling, thresholdCeiling, n₀Floor, CsFloor, fun _ => 0⟩, ⟨hQ, h1, h2⟩,
    fun T hAdm hMet => ?_⟩
  obtain ⟨y₀, f⟩ := hT T hAdm hMet.side_ge hMet.rt_le hMet.threshold_le hMet.n₀_ge hMet.Cs_ge hMet.derivBound_ge
    hMet.holds
  refine ⟨y₀, fun y hy s hs => ?_⟩
  obtain ⟨D, hData⟩ := f y hy
  have hrate : 0 < D.rateBound := by
    have hside : (1 : ℝ) < T.side := by
      have h : 2 ^ 40 ≤ T.side := hAdm.L_ge
      have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
      exact_mod_cast h'
    have hlog := Real.log_pos hside
    have hpi := Real.pi_pos
    show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    positivity
  obtain ⟨-, hHas⟩ := hData s D.rateBound hs hrate le_rfl
  have hEq : 3 / 4 * (asymptoticFreedomSlope * Real.log T.side) = D.rateBound := by
    show 3 / 4 * (asymptoticFreedomSlope * Real.log T.side) = 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    unfold asymptoticFreedomSlope
    field_simp
    norm_num
  rw [hEq]
  refine ⟨|(D.withShift s D.rateBound).c₅|, abs_nonneg _, (D.withShift s D.rateBound).floorStar,
    fun g hg hy₂ => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    obtain ⟨K, hK⟩ := hHas.passage g hg hy₂ β hβ
    exact ⟨K, hβ, hK.isFirstPassageIndex⟩
  · intro K β hp
    obtain ⟨K', hK⟩ := hHas.passage g hg hy₂ β hp.1
    obtain rfl : K' = K := firstPassageIndex_unique hK.isFirstPassageIndex hp.2
    refine ⟨hK.lower_bound, hK.upper_bound.trans ?_⟩
    have hc := le_abs_self (D.withShift s D.rateBound).c₅
    have h3 : (β - g ^ (-2 : ℤ) - s + (D.withShift s D.rateBound).c₅) / D.rateBound ≤
        (β - g ^ (-2 : ℤ) - s + |(D.withShift s D.rateBound).c₅|) / D.rateBound :=
      div_le_div_of_nonneg_right (by linarith) hrate.le
    exact add_le_add_right h3 1
  · intro K β hp k hk
    obtain ⟨K', hK⟩ := hHas.passage g hg hy₂ β hp.1
    obtain rfl : K' = K := firstPassageIndex_unique hK.isFirstPassageIndex hp.2
    exact hK.coupling_gt k hk
  · exact (hHas.members g hg hy₂).2.1
  · refine ⟨(D.withShift s D.rateBound).ratioError g, (hHas.ratio g hg hy₂).1, fun K β hK hp => ?_⟩
    rw [asymptoticFreedomSlope_eq_logSlope]
    exact (hHas.ratio g hg hy₂).2 K β hK hp
end YangMills.Construction.TotalDensitiesGiveASystem
end
