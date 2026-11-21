import YangMills.Construction.Towers.IteratesOfTheLinearMapsAsMeansOverBlocks
import YangMills.Construction.Towers.IteratesOfTheLinearMapsAsMeansOverBlocksOfTheWholeLattice
import YangMills.Construction.Towers.LinearMapsAreOnto
import YangMills.Construction.Towers.LinearMapsOfTheWholeLatticeAreOnto
import YangMills.Construction.Towers.LinearMapsOnConstantForms
import YangMills.Construction.Towers.LinearMapsOnConstantFormsOfTheWholeLattice
import YangMills.Construction.Towers.LinearMapsOnFormsSupportedOnPivotBonds
import YangMills.Construction.Towers.LinearMapsOnFormsSupportedOnPivotBondsOfTheWholeLattice
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMaps
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOnTheWholeLattice
import YangMills.Construction.Towers.RelationsOfTheLinearMapsAtTheTrivialConfiguration
import YangMills.Construction.Towers.RelationsOfTheLinearMapsOfAStep
import YangMills.Construction.Towers.RelationsOfTheLinearMapsOfAStepOfTheWholeLattice
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.TrivialLinearization
theorem allRelations_holds
    (hStep : TrivialLinearization.OneStepIdentitiesHold)
    (hConstant : LinearizationFacts.constantFormsStatement)
    (hPivot : LinearizationFacts.pivotFormsStatement)
    (hOnto : LinearizationFacts.surjectivityStatement)
    (hIterates : IterateIdentitiesStatement)
    (hAverages : IteratesAsCubeAverages)
    (hStepFull : FullSpace.TrivialLinearization.OneStepIdentitiesHold)
    (hConstantFull : FullSpace.LinearizationFacts.constantFormsStatement)
    (hPivotFull : FullSpace.LinearizationFacts.pivotFormsStatement)
    (hOntoFull : FullSpace.LinearizationFacts.surjectivityStatement)
    (hIteratesFull : FullSpace.IterateIdentitiesStatement)
    (hAveragesFull : FullSpace.IteratesAsCubeAverages.Statement) :
    AllRelationsStatement := by
  intro L hL
  refine ⟨fun n k j m hn hj hm => ?_, fun k j m hj hm => ?_⟩
  · exact ⟨hStep L hL n k j hn hj, hConstant L hL n k j hn hj, hPivot L hL n k j hn hj,
      hOnto L hL n k j m hn hj hm, hIterates L hL n k m hn hm, hAverages L hL n k m hn hm⟩
  · exact ⟨hStepFull L hL k j hj, hConstantFull L hL k j hj, hPivotFull L hL k j hj,
      hOntoFull L hL k j m hj hm, hIteratesFull L hL k m hm, hAveragesFull L hL k m hm⟩
end YangMills.Construction.Tower.TrivialLinearization
