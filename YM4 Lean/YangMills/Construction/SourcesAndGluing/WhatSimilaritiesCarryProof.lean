import YangMills.Construction.SourcesAndGluing.SimilarityCarriesArrays
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesCellAlgebras
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesExpectationsAndObservables
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesGridSidesAndCells
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesLipschitzFunctions
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesPeriodicGibbsStates
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesTheGroup
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesTheInfiniteLattice
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesTheTorusLattice
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesToTheStandardOffset
import YangMills.Construction.SourcesAndGluing.WhatSimilaritiesCarry
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
theorem rescalingTransportClaim_holds
    (hInfinite : RescalingMapsInfiniteLatticeClaim)
    (hTorus : RescalingMapsPeriodicLatticeClaim)
    (hObservables : RescalingKeepsExpectationsAndObservables.Statement)
    (hLipschitz : RescalingLipschitzClaim)
    (hGibbs : RescalingGibbsClaim)
    (hCubes : RescalingKeepsGridScalesAndCubes.Statement)
    (hAlgebras : LatticeRescalingCubeAlgebrasClaim)
    (hGroup : RescalingConjugatesGroupClaim)
    (hProducts : LatticeRescalingReflectionProductsClaim)
    (hOrigin : RescalingNormalizesOriginClaim) :
    RescalingTransportClaim :=
  ⟨fun D Ψ => ⟨hInfinite D Ψ, hTorus D Ψ, (hObservables D Ψ).1, (hObservables D Ψ).2.1,
    (hLipschitz D Ψ).1, (hObservables D Ψ).2.2, (hLipschitz D Ψ).2, hGibbs D Ψ, (hCubes D Ψ).1,
    fun g hg => ⟨(hCubes D Ψ).2 g hg, hAlgebras D Ψ g hg, hGroup D Ψ g hg, hProducts D Ψ g hg⟩⟩,
    hOrigin⟩
end YangMills.Construction.SourcesAndGluing
end
