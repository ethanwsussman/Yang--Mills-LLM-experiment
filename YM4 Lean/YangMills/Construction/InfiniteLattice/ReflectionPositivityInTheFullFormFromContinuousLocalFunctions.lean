import YangMills.Construction.InfiniteLattice.MirrorsOfTheSixteenFamiliesAndTheClassOfReflectionPositiveStates
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.FullReflectionPositivityFromContinuousLocal
def Statement : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (Q : LatticeConventions.NormalHyperplane) (hQ : Q.IsLatticeMirror a)
    (ν : BorelProb a),
    InfiniteLattice.IsSymmetricUnder ν.1 (LatticeConventions.NormalHyperplane.reflectSymmetry hQ) →
    (∀ F ∈ locallyMeasurableIn a Q.upperHalfSpace, Continuous F → 0 ≤ reflectedPairing hQ ν F) →
    IsFullyReflectionPositive hQ ν
end YangMills.Construction.GibbsAtFixedSpacing.FullReflectionPositivityFromContinuousLocal
end
