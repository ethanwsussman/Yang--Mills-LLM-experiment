import YangMills.Construction.ParameterData.ScaleSequenceData
import YangMills.Construction.TotalDensitiesGiveASystem.TheWindowsRecur
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open TrajectoryData
theorem firstPassageWindowsRecur_of_pathData (htrack : trajectoryDataStatement) :
    FirstPassageWindowsRecur := by
  obtain ⟨Q, hQ, sideFloor, rateCeiling, thresholdCeiling, n₀Floor, CsFloor, C₀, h1, h2, hT⟩ := htrack
  refine ⟨⟨Q, sideFloor, fun _ => C₀, rateCeiling, thresholdCeiling, n₀Floor, CsFloor, fun _ => 0⟩,
    ⟨hQ, h1, h2⟩, fun T hadm hmet => ?_⟩
  obtain ⟨y₀, f⟩ := hT T hadm hmet.side_ge hmet.rt_le hmet.threshold_le hmet.n₀_ge hmet.Cs_ge
    hmet.derivBound_ge hmet.holds
  refine ⟨y₀, fun y hy => ?_⟩
  obtain ⟨D, hdata⟩ := f y hy
  have hrate : 0 < D.rateBound := by
    have hL : (1 : ℝ) < T.side := by
      have h : 2 ^ 40 ≤ T.side := hadm.L_ge
      have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
      exact_mod_cast h'
    have hlog := Real.log_pos hL
    have hpi := Real.pi_pos
    show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    positivity
  obtain ⟨-, hhas⟩ := hdata (2 * T.B) D.rateBound le_rfl hrate le_rfl
  refine ⟨max 1 (D.withShift (2 * T.B) D.rateBound).windowCount, le_max_left _ _,
    (D.withShift (2 * T.B) D.rateBound).floorStar, fun g hg hy₂ K' => ?_⟩
  obtain ⟨K, hK, hle, β, hβ⟩ := (hhas.members g hg hy₂).2.2 K'
  exact ⟨K, hK, le_trans hle (Nat.add_le_add_left (le_max_right _ _) _), β, hβ⟩
end YangMills.Construction.TotalDensitiesGiveASystem
end
