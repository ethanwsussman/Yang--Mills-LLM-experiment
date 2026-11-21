import YangMills.Construction.MirrorGridsOfEverySide.SimilaritiesOfTheLattices
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesCellFunctions
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesCellFunctionsOnTheTori
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesCellsAndGroupOnTheTori
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesCellsAndGroupProof
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesSidesAndOffsets
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesTheInfiniteLattice
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesTheMeasures
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides.ScalingMapFacts
private theorem torusSide_image {D : GridSetup} (S : ScalingMap D) :
    PeriodicLattice.torusSide S.image.L S.image.m = S.scale * PeriodicLattice.torusSide D.L D.m := by
  change 2 * (D.L : ℝ) ^ ((D.m : ℕ) + S.power) = (D.L : ℝ) ^ S.power * (2 * (D.L : ℝ) ^ (D.m : ℕ))
  rw [pow_add]
  ring
abbrev _root_.YangMills.SharedProofs.p15016 := @torusSide_image
private theorem cellSide_gridImage {D : GridSetup} (S : ScalingMap D)
    (g : ChessboardTori.ReflectionGrid D) :
    (S.gridImage g).cellSide = S.scale * g.cellSide := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ScalingProof.cellSide_gridImage <;> assumption
theorem scalingMapTheorem_of_parts
    (hGrid : ScalingPreservesGridPoints)
    (hTorus : ScalingPreservesTorus)
    (hMeasure : ScalingPreservesMeasures)
    (hSides : ScalingPreservesSidesAndCentres)
    (hCells : ScalingPreservesCellsAndGroup)
    (hObs : ScalingPreservesCellObservables)
    (hCellsTorus : ScalingPreservesCellsAndGroupTorus)
    (hObsTorus : ScalingPreservesCellObservablesTorus) :
    ScalingMapTheorem := by
  intro D S
  have hb := S.power_lt
  refine ⟨⟨by omega, ?_, ?_, torusSide_image S⟩, hGrid D S, hTorus D S, hMeasure D S, hSides D S,
    fun g hg =>
      ⟨cellSide_gridImage S g, rfl, ⟨hCells D S g hg, hObs D S g hg⟩,
        fun hl => ⟨hCellsTorus D S g hg hl, hObsTorus D S g hg hl⟩⟩⟩
  · exact ⟨(D.m : ℕ) + S.power, Nat.add_pos_left D.m.pos _, (torusSide_image S).symm⟩
  · change (((D.K : ℕ) - S.power : ℕ) : ℤ) = ((D.K : ℕ) : ℤ) - (S.power : ℤ)
    omega
end YangMills.Construction.MirrorGridsAllSides.ScalingMapFacts
end
