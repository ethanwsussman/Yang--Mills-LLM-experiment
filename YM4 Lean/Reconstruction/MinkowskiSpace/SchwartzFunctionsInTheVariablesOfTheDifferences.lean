import Reconstruction.MinkowskiSpace.BoundaryValuesOnTheTube
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.DifferenceVariables
def SchwartzInDifferences : Prop :=
  ∀ n : ℕ,
    MeasurePreserving
      (MinkowskiSpace.cumulativeSums : TestSpaces.PointTuple (n + 1) → TestSpaces.PointTuple (n + 1))
      volume volume ∧
    (∀ x Y : TestSpaces.PointTuple (n + 1),
      MinkowskiSpace.diffCoords
          (MinkowskiSpace.tupleToComplex (MinkowskiSpace.cumulativeSums x) +
            Complex.I • MinkowskiSpace.tupleToComplex (MinkowskiSpace.cumulativeSums Y)) =
        TubeBoundary.tubePoint x Y) ∧
    ∀ f : TestSpaces.PointTuple (n + 1) → ℂ, f ∈ TestSpaces.schwartzSet (n + 1) →
      RealPointVectors.diffCoords f ∈ TestSpaces.schwartzSet (n + 1) ∧
      (∀ j : ℕ, RealPointVectors.timeWeightedDeriv^[j] f ∈ TestSpaces.schwartzSet (n + 1)) ∧
      (∀ j : ℕ, TubeBoundary.totalTimeDeriv^[j] (RealPointVectors.diffCoords f) =
        RealPointVectors.diffCoords (RealPointVectors.timeWeightedDeriv^[j] f)) ∧
      ∀ k : ℕ, TubeBoundary.maxTimeDerivNorm k (RealPointVectors.diffCoords f) =
        RealPointVectors.maxTimeDerivL1 k f
end YangMills.Construction.DifferenceVariables
