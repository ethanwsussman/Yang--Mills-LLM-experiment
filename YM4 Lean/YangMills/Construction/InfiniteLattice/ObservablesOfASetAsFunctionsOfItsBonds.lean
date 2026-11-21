import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.InfiniteLattice.WhatAnObservableReads
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.InfiniteLattice
open FieldsAtSpacing
def RegionObservablesAsLinkFunctions : Prop :=
  ∀ a : ℝ, 0 < a →
    (∀ S : Set AmbientSpace,
      IsUnitalStarClosed (regionObservables a S) ∧
        IsUnitalStarClosed (boundedSubsetObservables a S)) ∧
    (∀ S T : Set AmbientSpace, S ⊆ T →
      regionObservables a S ⊆ regionObservables a T ∧
        boundedSubsetObservables a S ⊆ boundedSubsetObservables a T) ∧
    (∀ (S : Set AmbientSpace) (A : FieldSpace a → ℂ), IsBoundedObservable A →
      [A ∈ regionObservables a S,
        FactorsThroughLinks (positiveLinksWithin a S) A,
        DependsOnlyOnLinks (linksWithin S) A].TFAE) ∧
    (∀ S : Set AmbientSpace, IsClosed S →
      regionObservables a S = {A | FactorsThroughLinks (linksWithin S) A})
end YangMills.Construction.InfiniteLattice
