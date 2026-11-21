import YangMills.Construction.LawOnABoxOfTheFlow.SitesOfTheHullAreRare
import YangMills.Construction.ResponseInTheExpansion.TheHullIsRareAtASite
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxEvents
theorem hullSiteRare_of_hullRareAtSite (hH : ResponseInTheExpansion.hullRareAtSiteStatement) :
    hullSiteRareStatement := by
  intro a ha
  obtain ⟨L₀, r₀, hr₀, h⟩ := hH a ha
  refine ⟨L₀, r₀, hr₀, fun L hL hLge Tb hTa hTL hDr hrt => ?_⟩
  obtain ⟨y₀, hy₀⟩ := h L hL hLge Tb hTa hTL hDr hrt
  refine ⟨y₀, fun y hy hRet hWil => ⟨0, fun T β k n _ hst hco _ hn hside z => ?_⟩⟩
  obtain ⟨e, he⟩ := hn
  have hx : (T.stage k).coupling = flowCoupling (Tb.stepParameters y) β k :=
    hst.coupling_eq k (Nat.le_succ k)
  have hb := hy₀ y hy hRet hWil T β k e n he hst hco (by rw [hx]; exact hside) z
  rw [hx] at hb
  exact hb
end YangMills.Construction.BoxEvents
end
