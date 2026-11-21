import YangMills.Construction.Towers.ChainRuleAtAFiniteSideInTheLeftChart
import YangMills.Construction.Towers.ChainRuleAtTheSideInfinityInTheLeftChart
import YangMills.Construction.Towers.CurvesAtAFiniteSideInTheLeftChart
import YangMills.Construction.Towers.CurvesAtTheSideInfinityInTheLeftChart
import YangMills.Construction.Towers.FactsOfTheLeftChart
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChart
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChart
import YangMills.Construction.Towers.IsometriesInTheLeftChart
import YangMills.Construction.Towers.TangentVectorsInTheLeftChart
import YangMills.Construction.Towers.WritingsOfAChainInTheLeftChart
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
theorem leftChartFacts_holdEverywhere_of
    (tangent : LeftChartTangentSpaces)
    (curves : FiniteLevelCurveDifferentials.Statement)
    (chain : FiniteLevelChainRule.Statement)
    (fullCurves : FullSpaceCurveDifferentials.Statement)
    (writings : LeftChartChainRule)
    (fullChain : FullSpaceChainRule.Statement)
    (directions : GaugeOrbitTangentInLeftChart.Statement)
    (gauge : GaugeEquivarianceFormsAllSides)
    (symmetries : LeftChartIsometryEquivariance) :
    LeftChartFacts.HoldEverywhere := by
  intro L k j j' j'' hL hj hj' hj''
  have d := directions L k j hL hj
  have g := gauge L k j hL hj
  have s := symmetries L k j hL hj
  exact ⟨tangent.1,
    fun n hn => ⟨tangent.2 L k j hL hj n hn, curves L k j j' hL hj hj' n hn,
      chain L k j j' j'' hL hj hj' hj'' n hn, d.1 n hn, g.1 n hn, s.1 n hn⟩,
    fullCurves L k j j' hL hj hj', fullChain L k j j' j'' hL hj hj' hj'',
    writings L k j j' j'' hL hj hj' hj'', d.2, g.2, s.2⟩
end YangMills.Construction.Tower
