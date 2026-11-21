import YangMills.Construction.FourPointCondition.FourPointBoundAlongTheFlow
import YangMills.Construction.FourPointCondition.FourPointConditionForAnyChoice
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set Topology YangMills.Construction.ResponseInTheExpansion YangMills.Construction.WeightedResponses
namespace YangMills.Construction.FourPointCondition
private theorem natSuccCast_isSubexpGrowth :
    RoomFunctions.IsSubexpGrowth fun s : ℕ => (s : ℝ) + 1 where
  mono := fun m n hmn => by
    have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
    simpa using hcast
  one_le_apply := fun s => by
    linarith
  tendsto_atTop_atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  tendsto_log_div_nat := by
    have hlim : Tendsto (fun s : ℕ => (s : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hlogDiv : Tendsto (fun s : ℕ => Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1)) atTop (𝓝 0) :=
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hlim
    have hratio : Tendsto (fun s : ℕ => 1 + 1 / (s : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    have hprod := hlogDiv.mul hratio
    rw [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hspos
    have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast hspos.ne'
    have hsne' : (s : ℝ) + 1 ≠ 0 := by positivity
    field_simp
theorem fourPointBoundAtFlowData (hLaws : lawsAtFlowDataStatement)
    (hEvery : fourPointBoundAtEveryProfile) : fourPointBoundAtFlowDataStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, hLawsAt⟩ := hLaws a ha
  obtain ⟨L₂, r₂, C₂, hr₂, hEveryAt⟩ := hEvery a ha
  refine ⟨max (max L₁ L₂) 2, fun c => min (r₁ c) (r₂ c), max C₁ C₂,
    fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hOdd hL T hTa hTL hDrawn hCold hOn hrt hCder
  have hL₁ : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL₂ : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL₃ : 2 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨y₁, hy₁⟩ := hLawsAt L hOdd hL₁ T hTa hTL hDrawn hCold hOn
    (le_trans hrt (min_le_left _ _)) (le_trans (le_max_left _ _) hCder)
  obtain ⟨y₂, hy₂⟩ := hEveryAt L hOdd hL₂ T hTa hTL hDrawn hCold hOn
    (le_trans hrt (min_le_right _ _)) (le_trans (le_max_right _ _) hCder)
  refine ⟨max y₁ y₂, fun y hy hReturns hRow => ?_⟩
  obtain ⟨Kr, -, hData⟩ := hy₁ y (le_trans (le_max_left _ _) hy) hReturns hRow
  have hCentered := hy₂ y (le_trans (le_max_right _ _) hy) hReturns hRow
  intro D hHas shift hShift g hg hFloor
  obtain ⟨al, -, hAt⟩ := hData D hHas
  have hRate : 0 < D.rateBound := by
    have hlog : 0 < Real.log (T.side : ℝ) := by
      rw [hTL]
      exact Real.log_pos (by exact_mod_cast (by omega : 1 < L))
    have hpi : 0 < Real.pi := Real.pi_pos
    show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log (T.side : ℝ))
    positivity
  refine ⟨fun K₀ => ?_, fun vt hvt₀ hvt₁ room hRoom => ?_⟩
  · obtain ⟨d₀, ηBar, εBar, -, -, hLarge⟩ :=
      hAt shift D.rateBound hShift hRate le_rfl 1 one_pos le_rfl g hg hFloor
        _ natSuccCast_isSubexpGrowth
    obtain ⟨K, β, hK, hβ⟩ := hLarge K₀
    exact ⟨K, β, hK, hβ⟩
  · obtain ⟨d₀, ηBar, εBar, hPullback, -, -⟩ :=
      hAt shift D.rateBound hShift hRate le_rfl vt hvt₀ hvt₁ g hg hFloor room hRoom
    obtain ⟨d₄, hd₄, hAtData⟩ := hCentered vt hvt₀ hvt₁ _ _ _ _ _ hPullback
    exact ⟨d₄, hd₄.1, fun _ => hAtData⟩
end YangMills.Construction.FourPointCondition
end
