import YangMills.Construction.InfiniteLattice.PeriodicExtensionsStatesAndTorusFunctionalsAtOneSpacing
import YangMills.Construction.InfiniteLattice.SpecificationDensitiesAndTheDensityDistanceAtOneSpacing
import YangMills.Construction.Probability.BoundedComplexExpectation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction
namespace FixedSpacing
def KernelPreservesTorusExpectation.Statement : Prop :=
  ∀ (D : Setup) (W : LinkWindow D.mesh) (S : Set (Link D.mesh)) (F : D.Fields → ℂ),
    FactorsThroughFinite S F → ∀ r : ℝ, 0 ≤ r →
      (∀ e ∈ (W.links : Set (Link D.mesh)) ∪ S,
        (e.initial : AmbientSpace) ∈ closedCube r ∧ (e.terminal : AmbientSpace) ∈ closedCube r) →
      r + D.mesh < D.side / 2 →
      Probability.complexExpectation D.liftedGibbs (D.conditionalKernel W F) =
        Probability.complexExpectation D.liftedGibbs F
end FixedSpacing
end YangMills.Construction
