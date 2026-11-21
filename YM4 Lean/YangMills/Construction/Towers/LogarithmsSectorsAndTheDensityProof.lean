import YangMills.Construction.Towers.GaugeTransformationsKeepTheDensity
import YangMills.Construction.Towers.KeepingTheDensityGivesItsSymmetry
import YangMills.Construction.Towers.LogarithmOfAShiftedOperatorAndIntertwiners
import YangMills.Construction.Towers.LogarithmOnTheSectorsOfSitesAndBonds
import YangMills.Construction.Towers.LogarithmsOfTheAbelianOperators
import YangMills.Construction.Towers.LogarithmsSectorsAndTheDensity
import YangMills.Construction.Towers.MultiplesOfTheSectorMatricesAndTheConjugation
import YangMills.Construction.Towers.ShiftKeepsTheDensity
import YangMills.Construction.Towers.TheDensityIsTheSumOverTheSectorsOnTheUnitLattice
import YangMills.Construction.Towers.TheDensityUnderTheConjugation
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2
namespace YangMills.Construction.Tower.AbelianFieldDensity
open SectorDecomposition in
theorem logSectorsAndDensity_holds
    (hLog : LogShiftedAndIntertwiners)
    (hWeights : WeightMultiplesAndStar)
    (hOnSector : LogOnVertexAndEdgeSectors)
    (hSplit : UnitLatticeTraceSplits.Claim)
    (hStar : UnitLatticeStarConj.Claim)
    (hAbelian : AbelianOperatorLogarithms)
    (hGauge : GaugeKeepsTraceDensity)
    (hShift : TranslationPreservesTrace)
    (hInvariance : DensityPreservationGivesInvariance) :
    LogSectorsAndDensity := by
  refine ⟨fun H H' _ _ _ _ _ _ z hz => ?_, fun L hL z hz => ?_⟩
  · obtain ⟨hHead, -, hInter⟩ := hLog H H' z hz
    exact ⟨hHead, hInter⟩
  · obtain ⟨hEdge, hMem, hVert, hEdgeVal, hStarVert, hStarEdge, -, -⟩ := hWeights L hL
    obtain ⟨hSecVert, hSecEdge⟩ := hOnSector L hL z hz
    obtain ⟨hSplitVert, hSplitEdge⟩ := hSplit L hL
    obtain ⟨hConjVert, hConjEdge⟩ := hStar L hL
    exact ⟨hEdge, hMem, hVert, hEdgeVal, hStarVert.ofCoords_eq_fieldStar,
      hStarEdge.ofCoords_eq_fieldStar,
      (hLog (L2Field (FullSpace.Vertex L 0 0))
        (L2Field (FullSpace.Vertex L 0 0)) z hz).2.1,
      (hLog (L2Field (PeriodicOperators.PosEdge L 0 0))
        (L2Field (PeriodicOperators.PosEdge L 0 0)) z hz).2.1,
      fun N' _ => (hLog (VectorL2 L N') (VectorL2 L N') z hz).2.1,
      hSecVert, hSecEdge, hSplitVert, hSplitEdge, hConjVert, hConjEdge,
      fun θ hθ => hAbelian L hL z hz θ hθ,
      fun u hu => hInvariance L hL z hz 0 _ _ (hGauge L hL u hu).1 (hGauge L hL u hu).2,
      fun n => hInvariance L hL z hz n _ _ (hShift L hL n).1 (hShift L hL n).2⟩
end YangMills.Construction.Tower.AbelianFieldDensity
