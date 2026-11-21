import YangMills.Construction.Continuum.FunctionalsWithAOnePointFunction
import YangMills.Construction.Continuum.GrowthConditionFromAPowerBoundOnSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PowerBoundFunctionalGrowth
open TestSpaces
open SeparatedBound
open SeparatedPowerBound
def cumulantFamily (σ : TestSpaces.SepTuple → ℝ) : CorrelationFamily :=
  fun _ _ X => cumulant σ X
def GrowthOfFunctionalFromPowerBound : Prop :=
  ∀ (M : ℝ) (a : ℕ) (C k cBar 𝔠 : ℝ) (σ : TestSpaces.SepTuple → ℝ), 1 ≤ M → 0 ≤ C → 0 ≤ k →
    0 ≤ cBar → IsSepFunctional σ →
    (∀ X : SepTupleOfCard 1, cumulant σ X = 𝔠 * ∫ u, X.1 0 u) → |𝔠| ≤ cBar →
    PowerSepBound M a C k (cumulantFamily σ) →
    ∀ ϰ : ℝ, 20 + k ≤ ϰ →
      GrowthBound (10 + a) (1 + 2 * extFactorAbs)
        (onePointConst (10 + a) (powerBase M a C) cBar) ϰ σ
end YangMills.Construction.PowerBoundFunctionalGrowth
end
