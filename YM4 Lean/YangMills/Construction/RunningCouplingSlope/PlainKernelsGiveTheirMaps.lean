import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators Matrices Conventions
def MeanKernelsRepresent : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      (∀ j < k, Represents (meanStepKernel L n k U j)
        ((edgePauliCoordinates L n k j).mapOnCoeffs (edgePauliCoordinates L n k (j + 1))
          fun B => (L : ℝ)⁻¹ • meanCovariantStep (meanIterate U j) B)) ∧
      Represents (meanKernelQ L n k U) ((edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
        fun B => finestMesh L k • meanCovariant U k B) ∧
      Represents (meanKernelR L n k U) ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs
        (vertexCoordinate (Vertex L n k k)) (composedCubeAverage (quietPoint U) k)) ∧
      (∀ j ≤ k, ∀ B ∈ edgeFormSpace L n k 0, meanCovariant U j B ∈ edgeFormSpace L n k j) ∧
      (∀ j ≤ k, ∀ l : Vertex L n k 0 → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) →
        ∀ y, composedCubeAverage (quietPoint U) j l y ∈ ComplexMatrix2.hermitianTraceless) ∧
      (∀ B ∈ complexEdgeForms L n k 0, ∀ B' ∈ complexEdgeForms L n k 0, ∀ w : ℂ,
        meanCovariant U k (w • B + B') = w • meanCovariant U k B + meanCovariant U k B') ∧
      ∀ l l' : Vertex L n k 0 → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        (∀ x, l' x ∈ ComplexMatrix2.traceless) → ∀ w : ℂ,
        composedCubeAverage (quietPoint U) k (w • l + l') =
          w • composedCubeAverage (quietPoint U) k l + composedCubeAverage (quietPoint U) k l'
end YangMills.Construction.RunningCouplingSlope
end
