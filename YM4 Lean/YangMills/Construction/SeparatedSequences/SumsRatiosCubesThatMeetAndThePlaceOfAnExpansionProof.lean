import YangMills.Construction.SeparatedSequences.BareSitesNearATopLieInTheFirstMember
import YangMills.Construction.SeparatedSequences.DistanceRatiosAndSumsOverTheTops
import YangMills.Construction.SeparatedSequences.LevelsAndDistanceOfCubesThatMeet
import YangMills.Construction.SeparatedSequences.NeighbouringSitesAndBasePointsLieInCubesThatMeet
import YangMills.Construction.SeparatedSequences.NumberOfCubesThatMeetACube
import YangMills.Construction.SeparatedSequences.SumsRatiosCubesThatMeetAndThePlaceOfAnExpansion
import YangMills.Construction.SeparatedSequences.TopsOfTheBareSitesNearATop
import YangMills.Construction.SeparatedSequences.WeightedDistanceBetweenTheEndPointsOfAnExpansion
import YangMills.Construction.SeparatedSequences.WeightedDistanceDominatesTheLength
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SeparatedClasses
theorem ApexSumsAndMeetingBlocks.holds
    (hSums : ApexDistanceBoundsStatement)
    (hMeet : MeetingBlocksLevelAndDistance)
    (hNumber : SeparatedClasses.MeetingBlocksCount)
    (hNeighbours : AdjacentSitesInMeetingBlocks)
    (hNear : BareSitesNearApexInRegionZero)
    (hTops : ApexesNearFineSite)
    (hLength : LOneDistLeChainDist)
    (hRow : ExpansionEndpointsDistLe) :
    ApexSumsAndMeetingBlocks.Statement := by
  intro C hC Ω hΩ
  obtain ⟨h1, h2⟩ := hSums C hC Ω hΩ
  obtain ⟨h3, h4⟩ := hNeighbours C hC Ω hΩ
  exact ⟨h1, fun a ha => h2 a ha, hMeet C hC Ω hΩ, hNumber C hC Ω hΩ, h3, h4, hNear C hC Ω hΩ,
    hTops C hC Ω hΩ, hLength C hC Ω hΩ, hRow C hC Ω hΩ⟩
end YangMills.Construction.SeparatedClasses
