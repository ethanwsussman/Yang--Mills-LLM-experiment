import YangMills.Construction.Continuum.CoefficientsOfAFunctionOfASystemDecay
import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystem
import YangMills.Construction.Continuum.CostsOfTheSeriesOfASeparatedSystem
import YangMills.Construction.Continuum.FourierSeriesOfASystemAndTheCostOfAMode
import YangMills.Construction.Continuum.FunctionOfASystemSumsItsSeries
import YangMills.Construction.Continuum.ModesAreCutoffsTimesCharacters
import YangMills.Construction.Continuum.PartialSumsOfASystemApproachTheFunction
import YangMills.Construction.Continuum.SumOverIntegerPointsOfTheDecayWeight
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ConfigSpace
theorem fourierExpansionAndModeCosts_holds
    (hDecay : SystemCoeffsDecay)
    (hModes : ModesAreLocalCharacters)
    (hSeries : SystemFunctionHasExpansion)
    (hApprox : TruncationsApproachFunction)
    (hLattice : IntegerLatticeDecaySum)
    (hCost : ModeCostOfSeparated)
    (hSum : SeparatedSystemCostsSummable) :
    FourierExpansionAndModeCosts := by
  intro n hn Q Φ hΦ
  exact ⟨hDecay n hn Q Φ hΦ, hModes n hn Q, hSeries n hn Q Φ hΦ, hApprox n hn Q Φ hΦ,
    hLattice n hn, fun h2 hsep c a G T hT =>
      ⟨hCost n h2 Q hsep c a G T hT, hSum n h2 Q hsep Φ hΦ c a G T hT⟩⟩
end YangMills.Construction.ConfigSpace
