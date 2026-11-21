import YangMills.Construction.Continuum.GrowthConditionOfAFunctionalFromAPowerBound
import YangMills.Construction.Continuum.MultilinearityAndInversionOfTheConnectedFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PowerBoundFunctionalGrowth
open TestSpaces
open SeparatedBound
open SeparatedPowerBound
theorem growthOfFunctionalFromPowerBound_holds (hG : SeparatedPowerBound.GrowthFromPowerSepBound)
    (hO : TestSpaces.OnePointFunctional.growth)
    (hI : TestSpaces.CumulantMultilinearInversion) : GrowthOfFunctionalFromPowerBound := by
  intro M a C k cBar c σ hM hC hk hc hσ h1 hcb hP ϰ hϰ
  obtain ⟨-, hml, -, hcen, -⟩ := hI.1 σ hσ (cumulantFamily σ)
  have hcon := hG M a C k (cumulantFamily σ) hM hC hk (fun n hn => hml n (by omega)) hcen hP
  obtain ⟨-, hc', hL, hx, T, hT, hb⟩ := hcon.growthBound ϰ hϰ
  exact (hO (10 + a) ϰ (2 * extFactorAbs) (powerBase M a C) cBar c σ T (by omega) hx hc' hL hc hσ
    h1 hcb hT hb).2
end YangMills.Construction.PowerBoundFunctionalGrowth
end
