import YangMills.Construction.Towers.AveragingCommutesWithIsometriesAtTheSideInfinity
import YangMills.Construction.Towers.AveragingCommutesWithIsometriesOnTheSides
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantAtTheSideInfinity
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSides
import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfiguration
import YangMills.Construction.Towers.AveragingPolydiscRadiusExists
import YangMills.Construction.Towers.DifferentialOfTheAveragingAtTheSideInfinity
import YangMills.Construction.Towers.DifferentialOfTheAveragingOnTheSides
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
theorem smoothingNearIdentity_of_parts
    (hAnalytic : SmoothingAnalyticCovariantOnSides)
    (hDeriv : SmoothingDerivAtOneOnAllSides)
    (hEquiv : SmoothingEquivariantOnSides)
    (hAnalyticFull : FullSpace.AllStepsSmoothingAnalyticCovariant)
    (hDerivFull : FullSpace.SmoothingDerivAtOneAllScales)
    (hEquivFull : FullSpace.SmoothingEquivariantAllSteps)
    (hRadius : AdmissiblePolydiscRadiusExists) :
    SmoothingNearIdentity :=
  ⟨fun L hL =>
    ⟨fun n k j hn hj =>
        ⟨hAnalytic L hL n k j hn hj, hDeriv L hL n k j hn hj, hEquiv L hL n k j hn hj⟩,
      fun k j hj => ⟨hAnalyticFull L hL k j hj, hDerivFull L hL k j hj, hEquivFull L hL k j hj⟩,
      Classical.epsilon_spec (hRadius L hL)⟩,
    fun _ _ => ⟨fun l => polydiscRadius l.1, fun _ => rfl⟩⟩
end YangMills.Construction.Tower
