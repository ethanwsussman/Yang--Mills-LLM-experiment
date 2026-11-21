import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import YangMills.Construction.RunningCouplingSlope.SlopeOfTheCoupling
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
theorem flowDescendsLinearly_of_couplingHasSlope
    (hslope : YangMills.Construction.RunningCouplingSlope.CouplingHasSlope) :
    YangMills.Construction.WeightedResponses.FlowDescendsLinearly := by
  obtain ⟨cH, -, r₀, hr₀, hslope⟩ := hslope
  intro a _
  refine ⟨2, r₀, hr₀, fun L _ hL => ?_⟩
  have hc : 0 < YangMills.Construction.CouplingFlow.slopeConst L := ?_
  refine ⟨3 / 4 * YangMills.Construction.CouplingFlow.slopeConst L, 2 * cH a L, by positivity,
    fun T hTa hTL hT hr => ?_⟩
  obtain ⟨C, yₛ, -, hslope⟩ := hslope T hT hr
  refine ⟨max T.floorMin (max yₛ ((4 * C / YangMills.Construction.CouplingFlow.slopeConst T.side) ^ 4)),
    fun y hy hR hW => ?_⟩
  have hmin : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hys : yₛ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hpow : (4 * C / YangMills.Construction.CouplingFlow.slopeConst T.side) ^ 4 ≤ y :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hthr : YangMills.Construction.RunningCouplingSlope.slopeThreshold (max y yₛ) C
      (YangMills.Construction.CouplingFlow.slopeConst T.side) = y := by
    unfold YangMills.Construction.RunningCouplingSlope.slopeThreshold
    rw [max_eq_left hys, max_eq_left hpow]
  have hdrop := hslope y hmin hR hW
  rw [hthr] at hdrop
  intro β hβ j hj i hi
  have := (hdrop β i j hβ hi (fun k hk => hj k (lt_of_lt_of_le hk hi)) (fun l _ hl => hj l hl)).lower_le
  rw [hTa, hTL] at this
  exact this
  · unfold YangMills.Construction.CouplingFlow.slopeConst
    have hlog : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
    positivity
end YangMills.Construction.ResponseInTheExpansion
end
