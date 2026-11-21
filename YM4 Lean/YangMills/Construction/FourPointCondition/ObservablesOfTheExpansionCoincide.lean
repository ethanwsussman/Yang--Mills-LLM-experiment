import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def torusUrsellEqWeightedCurvatureStatement : Prop :=
  ∀ (L : ℕ) [NeZero L] (m K p : ℕ) (β : ℝ), 3 ≤ L → 1 ≤ m →
    ∀ f : Fin p → PeriodicLattice.FourTorus L m → ℝ,
    PeriodicLattice.torusUrsellFunction L m K β f =
      WeightedResponses.connectedCurvature β (WeightedResponses.fineSide L K (2 * L ^ m))
        fun i => WeightedResponses.testWeight L K m (f i)
end YangMills.Construction.FourPointCondition
end
