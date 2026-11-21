import YangMills.Construction.MirrorGridsOfEverySide.ActionOnTheCellAlgebrasAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.ActionOnTheCellAlgebrasOfTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.CellsOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.CentresAreSitesAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.CoarserGridOnSpaceAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.CoarserGridOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.CopiesOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.FacePlanesAreLinkMirrorsAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.FactsOfAMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.FiniteSetsOfCellsLieInACoarserCellAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsOfTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.IsometriesThatKeepTheFacePlanesAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.ReflectionsInTheFacePlanesOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.RulesOfTheCopiesAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.RulesOfTheCopiesOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.SideIsAnOddMultipleOfTheSpacingAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
theorem reflectionGridProperties_holds
    (h1 : CellSideOddMultipleEveryGrid)
    (h2 : AllGridsWallsBisectLinks)
    (h3 : AllGridsCellCentresInLattice)
    (h4 : AllGridsReflectionGroupActsOnCells)
    (h5 : AllGridsActOnCellObservables)
    (h6 : TransportLawsEveryGrid)
    (h7 : AllGridsTorusCellStructure)
    (h8 : AllGridsTorusGroupActsOnCells)
    (h9 : AllGridsTorusWallReflections)
    (h10 : AllGridsTorusActOnCellObservables)
    (h11 : TorusTransportLawsEveryGrid)
    (h12 : AllGridsLiftCompatibleWithTransport)
    (h13 : AllGridsWallPreservingSymmetries)
    (h14 : AllGridsCoarseningOnSpace)
    (h15 : AllGridsCoarseningOnTorus)
    (h16 : AllGridsFiniteCellsInCoarserCell) :
    ReflectionGridProperties :=
  fun D g h =>
    ⟨h1 D g h, h2 D g h, h3 D g h, h4 D g h, h5 D g h, h6 D g h,
      fun hl => ⟨h7 D g h hl, h8 D g h hl, h9 D g h hl, h10 D g h hl, h11 D g h hl,
        h12 D g h hl, h13 D g h hl⟩,
      fun g' k₀ hc hs => ⟨h14 D g h g' k₀ hc hs, fun hl' => h15 D g h g' k₀ hc hs hl'⟩,
      h16 D g h⟩
end YangMills.Construction.MirrorGridsAllSides
end
