import YangMills.Construction.Towers.AlgebraOfTheLeftChart
import YangMills.Construction.Towers.CovarianceOfTheDerivativesOfTheActionOnTheSides
import YangMills.Construction.Towers.ExpansionOfTheMoveAtTheSideInfinity
import YangMills.Construction.Towers.ExpansionOfTheMoveOnASide
import YangMills.Construction.Towers.GaugeConditionsOfTheAlgebraOfTheLeftChartOnASide
import YangMills.Construction.Towers.GaugeCovarianceOfTheDerivativesOfTheActionAtTheSideInfinity
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartAtTheSideInfinity
import YangMills.Construction.Towers.IsometriesKeepThePairingsAndTheSecondDerivativeAtTheSideInfinity
import YangMills.Construction.Towers.IsometriesOnExponentialsAndPlaquettesAtTheSideInfinity
import YangMills.Construction.Towers.IsometriesOnExponentialsAndPlaquettesOfASide
import YangMills.Construction.Towers.IsometryOnPairingsAndTheSecondDerivativeOnASide
import YangMills.Construction.Towers.MatrixFactsOfTheAlgebraOfTheLeftChart
import YangMills.Construction.Towers.SecondDerivativeAtTheSideInfinityOfFormsWithNoCommonPlaquette
import YangMills.Construction.Towers.SecondDerivativeInAGaugeDirectionAtTheSideInfinity
import YangMills.Construction.Towers.SecondDerivativeInAGaugeDirectionOnASide
import YangMills.Construction.Towers.SecondDerivativeOfFormsWithNoCommonPlaquetteOnASide
import YangMills.Construction.Towers.SumOfThePlaquetteTermsOnASide
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.LeftChartAlgebra
theorem allConjunctsHold_of_parts
    (hMat : Tower.LeftChartAlgebra.MatrixIdentities.Statement)
    (hFaces : Tower.LeftChartAlgebra.FaceSumFiniteSide)
    (hGauge : Tower.LeftChartAlgebra.GaugeConditionsFiniteSide)
    (hGaugeFull : Tower.LeftChartAlgebra.GaugeConditionsInfiniteSide)
    (hTwist : Tower.TwistExpansionOnTorus.Claim)
    (hTwistFull : Tower.FullSpaceTwistExpansionClaim)
    (hCov : Tower.LeftChartAlgebra.DerivativeCovarianceOnPeriodic)
    (hDisjoint : Tower.LeftChartAlgebra.HessianDisjointVanishFiniteSide)
    (hDir : Tower.LeftChartAlgebra.HessianGaugeDirectionFiniteSide)
    (hCovFull : Tower.FullSpace.ActionDerivativeCovariance.Claim)
    (hDisjointFull : Tower.FullSpaceHessianDisjointVanishes)
    (hDirFull : Tower.FullSpace.GaugeDirectionHessianClaim)
    (hSym : Tower.PeriodicSymmetriesActOnExpAndFaces)
    (hPair : Tower.SideSymmetryPairingHessian.Statement)
    (hSymFull : Tower.FullSpace.SymmetriesActOnExpAndFaces)
    (hPairFull : Tower.FullSpace.LeftChartAlgebra.SymmetriesPreservePairingsAndHessian) :
    Tower.LeftChartAlgebra.AllConditionsHold := by
  refine ⟨hMat.1, hMat.2.1, fun L k j hL hj => ⟨fun n hn => ?_, ?_⟩⟩
  · obtain ⟨hTerms, hAct⟩ := hFaces L n k j hL hn hj
    obtain ⟨hG, hUnit⟩ := hGauge L n k j hL hn hj
    refine ⟨⟨hTerms, hG, hUnit, hTwist L n k j hL hn hj, ?_, ?_⟩, hAct⟩
    · intro U u l B B' hU hu hl hB hB'
      obtain ⟨h₁, h₂⟩ := hCov L n k j hL hn hj U u B B' hU hu hB hB'
      exact ⟨h₁, h₂, hDisjoint L n k j hL hn hj U B B' hU hB hB',
        hDir L n k j hL hn hj U l B hU hl hB⟩
    · intro f U hf hm hU
      obtain ⟨h₁, h₂⟩ := hSym L n k j hL hn hj f U hf hm hU
      exact ⟨h₁, h₂, hPair L n k j hL hn hj f U hf hm hU⟩
  · obtain ⟨hG, hUnit⟩ := hGaugeFull L k j hL hj
    refine ⟨hG, hUnit, hTwistFull L k j hL hj, ?_, ?_⟩
    · intro U u l B B' hU hu hl hlf hB hB' hBf hB'f
      obtain ⟨h₁, h₂⟩ := hCovFull L k j hL hj U u B B' hU hu hB hB' hBf hB'f
      exact ⟨h₁, h₂, hDisjointFull L k j hL hj U B B' hU hB hB' hBf hB'f,
        hDirFull L k j hL hj U l B hU hl hlf hB hBf⟩
    · intro f U hf hm hU
      obtain ⟨h₁, h₂⟩ := hSymFull L k j hL hj f U hf hm hU
      exact ⟨h₁, h₂, hPairFull L k j hL hj f U hf hm hU⟩
end YangMills.Construction.Tower.LeftChartAlgebra
