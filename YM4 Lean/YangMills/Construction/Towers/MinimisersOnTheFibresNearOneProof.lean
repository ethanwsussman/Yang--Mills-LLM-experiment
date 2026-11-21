import YangMills.Construction.Towers.BranchFromMinimisersInTheChart
import YangMills.Construction.Towers.MinimisersOnTheFibresNearOne
import YangMills.Construction.Towers.SpacesOfFormsAtAFiniteSide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem fibreMinimisersNearOne_holds
    (hmin : ConstrainedMinima.ExistsMinimizerChart)
    (hchartStep : CriticalStepInExpChart)
    (hsection : MinimizerChartGivesFibreSection)
    (hfin : FiniteSideFormSpaces) :
    FibreMinimisersNearOne := by
  intro L n k i hL hn hi F hF hgrad hpos
  haveI := (hfin L n k i hL hn hi.le).1
  haveI := (hfin L n k (i + 1) hL hn hi).1
  letI : Fintype (PositiveEdge L n k i) := Fintype.ofFinite _
  letI : Fintype (PositiveEdge L n k (i + 1)) := Fintype.ofFinite _
  obtain ⟨T, hT, hbuild⟩ := hsection L n k i hL hn hi F hF hgrad hpos
  obtain ⟨N, O, W, r, z, w, hC, hS⟩ :=
    hmin _ _ _ _ (hchartStep L n k i hL hn hi F hF hgrad hpos).1 T hT
  exact hbuild N O W r z w hC hS
end YangMills.Construction.Tower
end
