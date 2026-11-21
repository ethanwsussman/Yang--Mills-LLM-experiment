import YangMills.Construction.LawByMomentsOfTheFlow.CouplingOfAPointIsPositive
import YangMills.Construction.LawByMomentsOfTheFlow.TheFlowAboveTheWindow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open LevelTestFunctions RenormalizationStepParameters
namespace MomentLaw
theorem scaleCouplingPos (hW : CouplingFlowAboveWindow) : scaleCouplingPosStatement := by
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L hL _ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅ Kr hK
  refine ⟨max Tb.floorMin 1, ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd S
  have hfits := d₁.fits y ((le_max_left _ _).trans hy)
  have hy1 : 1 ≤ y := (le_max_right _ _).trans hy
  have hstep : AdmissibleStep (Tb.stepParameters y) := ⟨hfits, hrow, fun β hβ => hw β hβ⟩
  obtain ⟨hflow, -⟩ := hW _ hstep g hg hgy S.β S.data.windowLevel S.window_le S.passage
  have hle : y ≤ S.scaleCoupling := hflow S.data.scaleLevel S.supAdmissible.scaleLevel_le
  linarith
end MomentLaw
end YangMills.Construction
end
