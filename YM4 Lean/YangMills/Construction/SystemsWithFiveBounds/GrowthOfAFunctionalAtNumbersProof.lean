import YangMills.Construction.Continuum.GrowthConditionOfAFunctionalFromAPowerBound
import YangMills.Construction.SystemsWithFiveBounds.GrowthOfAFunctionalAtNumbers
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SeparatedBound YangMills.Construction.SeparatedPowerBound
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
theorem functionalGrowthAtConstants_holds (hL : LimitGrowthAtConstants)
    (hF : YangMills.Construction.PowerBoundFunctionalGrowth.GrowthOfFunctionalFromPowerBound) :
    FunctionalGrowthAtConstants := by
  intro Fr N B s S Q hd hst hQ sigma c cBar hcBar hsigma h1 hc hS
  have hP := (hL Fr N B s S Q hd hst hQ).powerBound
  have hC₀ : 0 ≤ powerConst N :=
    (mul_pos B.admissible_constants.aStar_pos (B.admissible_constants.ballConst_pos 1 one_pos)).le
  refine hF _ N.sepExponent (powerConst N) N.factorialExponent cBar c sigma Fr.one_le_M hC₀
    B.admissible_constants.factorialExponent_nonneg hcBar hsigma h1 hc ?_ (20 + N.factorialExponent) le_rfl
  intro n hn d hd₀ X hX
  have h := hP n hn d hd₀ X hX
  rw [← hS n hn X] at h
  exact h
end YangMills.Construction.SystemsWithFiveBounds
end
