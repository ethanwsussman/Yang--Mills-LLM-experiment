import YangMills.Construction.ClusterExpansionOfAStep.ClassesAreCountedAtTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfAStepAreCounted
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
theorem RenormalizationStepParameters.ParameterAssignment.gasRate_pos (T : RenormalizationStepParameters.ParameterAssignment) (hT : T.Admissible) :
    0 < T.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
theorem ClusterBounds.clusterSumBound_holds (hc : TorusLumps.ClusterSumBound)
    (hf : TorusLumps.CouplingFloorExists) : ClusterBounds.ClusterSumBound := by
  intro T hT
  have hrate := T.gasRate_pos hT
  obtain ⟨y₂, hy₂⟩ := hf T.gasRate T.side T.rt hrate
  refine ⟨max T.floorMin y₂, fun y hy x hx n _ Y => ?_⟩
  have hadm : (T.stepParameters y).Admissible := hT.fits y ((le_max_left _ _).trans hy)
  have hfloor : (T.stepParameters y).RangeFloor T.gasRate := fun x' hx' =>
    hy₂ x' (((le_max_right _ _).trans hy).trans hx')
  exact hc (T.stepParameters y) T.gasRate hadm hrate hfloor x hx n Y
end YangMills.Construction
end
