import YangMills.Construction.FourPointCondition.ConditionInTheLimits
import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def FourPointLawInLimitsAt (L : ℕ) (IsPair : ℕ+ → ℝ → Prop) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∃ d₄ : ℝ, 0 < d₄ ∧ ∀ d ∈ Ioc (0 : ℝ) d₄,
    ∀ (Q : SystemsWithFiveBounds.PairSequence L IsPair) (S : LimitTheorem.CumulantFamily), Q.Defines S →
      ∀ X : TestSpaces.SepTupleOfCard 4, X.1 ∈ QuadrupleClasses.collinearQuadsR4 d θ →
        FourPointCondition.IsInLimitInterval θ d X.1 (S 4 (by norm_num) X)
def fourPointLawInLimits : Prop :=
  HoldsAtAdmissibleParameters fun T y => ∀ Bs : ℝ, 2 * T.B ≤ Bs → ForSmallCoupling fun g =>
    FourPointLawInLimitsAt (T.stepParameters y).side fun K β => IsFirstPassagePoint (T.stepParameters y) Bs g K β
end YangMills.Construction.TotalDensities
end
