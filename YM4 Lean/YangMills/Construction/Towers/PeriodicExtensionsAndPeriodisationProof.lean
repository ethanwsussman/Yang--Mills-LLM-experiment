import YangMills.Construction.Towers.BracketsAndTransposesOnThePairs
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescends
import YangMills.Construction.Towers.CovariantAveragesAtAPeriodicExtensionDescend
import YangMills.Construction.Towers.CovariantDifferenceAtAPeriodicExtensionDescends
import YangMills.Construction.Towers.ExtensionByZeroOfSiteFunctionsDescends
import YangMills.Construction.Towers.IteratedAveragesOfAPeriodicExtension
import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMaps
import YangMills.Construction.Towers.LocalKernelsAndMatricesOfLinearMaps
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.SecondDifferentialOfTheActionDescends
import YangMills.Construction.Towers.SecondOrderKernelAtAPeriodicExtensionDescends
import YangMills.Construction.Towers.SecondOrderTermsAtAPeriodicExtension
import YangMills.Construction.Towers.SumsProductsAndTransposesOfDescendingKernels
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.Periodisation
theorem periodisationHolds_of_parts (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hAlg : DescendingKernelAlgebra)
    (hMat : KernelsAndLinearMapMatrices)
    (hBr : PairBrackets.BracketsAndTransposes)
    (hBil : LocalBilinearKernels.Claim)
    (hCov : CovDiffAtLift.Claim)
    (hComm : BracketAtPeriodicLift.DescendsClaim)
    (hHess : HessianAtLifts.HessianDescendsAtLifts)
    (hIter : IterMeansOfLift.Claim)
    (hQuad : QuadraticTermsFormedAtLift)
    (hMeans : PeriodicLiftDescent.CovariantMeansDescend)
    (hZero : ZeroExtensionOfVertexFunctions.Claim)
    (hQK : QuadraticKernelAtExtensionDescends) : PeriodisationHolds := by
  intro L hL k m hm
  obtain ⟨a₁, a₂⟩ := hCells L hL k m hm
  obtain ⟨b₁, b₂⟩ := hMat L hL k m hm
  refine ⟨a₁, a₂, hAlg L hL k m hm, b₁, b₂, hBr L hL k m hm, hBil L hL k m hm, ?_, ?_⟩
  · intro j h V hV J hJ
    obtain ⟨c₁, c₂⟩ := hComm L hL k m hm j h V hV J hJ
    exact ⟨c₁, hCov L hL k m hm j h V hV, hHess L hL k m hm j h V hV, c₂⟩
  · intro hk U hU
    obtain ⟨d₁, d₂⟩ := hIter L hL k m hm hk U hU
    exact ⟨d₁, fun hs μ hμ => ⟨d₂ hs, hQuad L hL k m hm hk U hU hs, hMeans L hL k m hm hk U hU hs,
      hZero L hL k m hm hk, hQK L hL k m hm hk U hU hs μ hμ⟩⟩
end YangMills.Construction.LocalKernels.Periodisation
