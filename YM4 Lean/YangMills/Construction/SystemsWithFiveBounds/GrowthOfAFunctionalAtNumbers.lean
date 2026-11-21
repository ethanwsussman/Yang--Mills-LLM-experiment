import YangMills.Construction.SystemsWithFiveBounds.GrowthOfALimitAtNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open LimitGrowthFromCutoffBound (restrictToTestTuples)
open AmbientPoints (TupleMapFamily)
open TestSpaces (IsSepFunctional GrowthBound SepTuple SepTupleOfCard cumulant)
namespace SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily GibbsStateSequence)
open SeparatedBound (extFactorAbs)
def FunctionalGrowthAtConstants : Prop :=
  ∀ (F : StatedSideFamily) (N : BoundConstants), BoundsHoldAt F N → ∀ (s : Conventions.StandingParameters)
    (S : TupleMapFamily s .euclidean) (Q : GibbsStateSequence F.L), (∀ k, F.IsFirstPassage (Q.K k) (Q.β k)) →
    (∀ k, Q.gibbs k ∈ F.stateSet F.L (Q.K k) (Q.β k)) →
    Q.TendsToFamily S →
    ∀ (φ : SepTuple → ℝ) (c cBound : ℝ), 0 ≤ cBound → IsSepFunctional φ →
      (∀ X : SepTupleOfCard 1, cumulant φ X = c * ∫ u, X.1 0 u) → |c| ≤ cBound →
      (∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
        cumulant φ X = restrictToTestTuples S n hn X) →
      GrowthBound (growthOrder N) (1 + 2 * extFactorAbs) (growthConst F.M N cBound)
        (20 + N.factorialExponent) φ
end SystemsWithFiveBounds
end YangMills.Construction
end
