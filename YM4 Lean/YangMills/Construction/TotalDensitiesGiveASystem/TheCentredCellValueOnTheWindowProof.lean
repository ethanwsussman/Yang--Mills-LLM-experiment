import YangMills.Construction.SystemOfAdmissibleConstants.CentredCellValueOnTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheCentredCellValueOnTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheCouplingsGiveTheWindow
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TotalDensities
theorem windowCentredCell_of_chessboardBound (hcoup : TrajectoryCouplingsGiveWindow.Statement)
    (hcell : SystemOfAdmissibleConstants.CentredCellChessboardBound) :
    WindowCentredCell.Statement := by
  refine HoldsAtAdmissibleParameters.mono (hcoup _ hcell) fun T y _ h Bs hBs => ?_
  obtain ⟨y₂, f⟩ := h Bs hBs
  refine ⟨y₂, fun g hg hy => ?_⟩
  obtain ⟨D, rfl, C, hCpos, hD⟩ := f g hg hy
  refine ⟨C, 1, hCpos, zero_le_one, fun M hM E hEL hp c u hu hsupp hside ν hν => ?_⟩
  have hsupp' : tsupport u ⊆ TestFunctions.closedBallR4 c.centre (c.side / 4) := by
    rw [show c.side / 4 = 1 / 4 * c.side by ring]
    exact hsupp
  obtain ⟨hmem, hval⟩ := hD M hM E hEL hp c hside u hu hsupp' ν hν
  have hcentred : (fun U => ReflectionsAndOneInsertion.complexSmeared E u U -
        ∫ V, ReflectionsAndOneInsertion.complexSmeared E u V ∂ν) =
      ReflectedCopies.centredSmeared E u (∫ U, InfiniteLattice.smearedEnergy u U ∂ν) := by
    funext U
    show _ - _ = ReflectionsAndOneInsertion.complexSmeared E u U - _
    congr 1
    exact integral_ofReal
  rw [hcentred]
  refine ⟨hmem, fun m hm => ?_⟩
  rw [Real.rpow_neg_one]
  exact hval m hm hmem
end YangMills.Construction.TotalDensities
end
