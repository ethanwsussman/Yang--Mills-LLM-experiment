import YangMills.Construction.Towers.ActionOfTheDifferencesOnPlaneWaves
import YangMills.Construction.Towers.CalculusOfPlaneWaves
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunction
import YangMills.Construction.Towers.FormulasOfThePlaneWaveFunctions
import YangMills.Construction.Towers.FreeOperatorsAreRealOfFiniteRangeAndTrivialOnTheColour
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheBonds
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnThePlaquettes
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheSites
import YangMills.Construction.Towers.RelationsOfThePlaneWaveFunctions
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWaves
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.PlaneWaveCalculus
theorem planeWaveCalculusHolds_of_parts
    (hVertex : VertexCoeffsHold)
    (hEdge : PlaneWaveEdgeCoefficientsHold)
    (hFace : FaceCoeffsHold)
    (hFormulas : PlaneWaveSymbolFormulas.Holds)
    (hCoboundary : CoboundarySymbolsOnPlaneWaves)
    (hSmoothing : PlaneWaveSmoothingSymbols.SmoothingSymbolsHold)
    (hWeights : WeightRelationsHold)
    (hFree : FreeOperatorsRealLocal.Claim)
    (hMultiplier : PeriodicMultiplierMatrices.Claim) :
    PlaneWaveCalculusHolds := by
  intro L hL k hk
  refine ⟨?_, hVertex L hL k hk, hEdge L hL k hk, hFace L hL k hk, hFormulas L hL k hk,
    hCoboundary L hL k hk, hSmoothing L hL k hk, hWeights L hL k hk, hFree L hL k hk,
    fun υ hυ t ht => hMultiplier L hL k hk υ hυ t ht⟩
  intro m hm
  rw [PlaneWaves.mem_freqBox] at hm ⊢
  intro ν
  simpa using hm ν
end YangMills.Construction.Tower.PlaneWaveCalculus
