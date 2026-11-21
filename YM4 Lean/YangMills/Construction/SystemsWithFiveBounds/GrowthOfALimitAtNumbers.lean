import YangMills.Construction.BoundsOnEverySide.GrowthOfALimitAtAFrameOverTheBounds
import YangMills.Construction.Continuum.FunctionalsWithAOnePointFunction
import YangMills.Construction.Continuum.GrowthConditionFromAPowerBoundOnSeparatedTuples
import YangMills.Construction.Continuum.GrowthConditionOfAFunctionalOfFourSpace
import YangMills.Construction.SystemsWithFiveBounds.BoundsAtNumbers
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
abbrev powerConst (N : BoundConstants) : ℝ := N.aStar * N.ballConst 1
abbrev growthOrder (N : BoundConstants) : ℕ := 10 + N.sepExponent
abbrev growthBase (M : ℝ) (N : BoundConstants) : ℝ :=
  SeparatedPowerBound.powerBase M N.sepExponent (powerConst N)
abbrev growthConst (M : ℝ) (N : BoundConstants) (cBar : ℝ) : ℝ :=
  TestSpaces.onePointConst (growthOrder N) (growthBase M N) cBar
structure LimitGrowthAt {s : Conventions.StandingParameters} (M : ℝ) (N : BoundConstants)
    (S : AmbientPoints.TupleMapFamily s .euclidean) : Prop where
  powerBound : SeparatedPowerBound.PowerSepBound M N.sepExponent (powerConst N) N.factorialExponent
    (LimitGrowthFromCutoffBound.restrictToTestTuples S)
  consequences : SeparatedPowerBound.PowerGrowthConsequences M N.sepExponent (powerConst N)
    N.factorialExponent (LimitGrowthFromCutoffBound.restrictToTestTuples S)
  growth : ∀ κ' : ℝ, 20 + N.factorialExponent ≤ κ' →
    FourSpaceGrowth.GrowthBoundOf (growthOrder N) (2 * SeparatedBound.extFactorAbs)
      (growthBase M N) κ' (CumulantLimits.moments S)
  growthAt : ∀ cBar : ℝ, 0 ≤ cBar →
    FourSpaceGrowth.GrowthBoundOf (growthOrder N) (1 + 2 * SeparatedBound.extFactorAbs)
      (growthConst M N cBar) (20 + N.factorialExponent) (CumulantLimits.moments S)
def LimitGrowthAtConstants : Prop :=
  ∀ (F : StatedSideFamily) (N : BoundConstants), BoundsHoldAt F N →
    ∀ (s : Conventions.StandingParameters) (S : AmbientPoints.TupleMapFamily s .euclidean)
    (Q : BoundsOnEverySide.GibbsStateSequence F.L), (∀ k, F.IsFirstPassage (Q.K k) (Q.β k)) →
    (∀ k, Q.gibbs k ∈ F.stateSet F.L (Q.K k) (Q.β k)) →
    Q.TendsToFamily S → LimitGrowthAt F.M N S
end YangMills.Construction.SystemsWithFiveBounds
end
