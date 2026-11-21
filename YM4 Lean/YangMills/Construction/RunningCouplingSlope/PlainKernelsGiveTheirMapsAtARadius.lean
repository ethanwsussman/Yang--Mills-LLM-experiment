import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
def MeanKernelsRepresent.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ r : ℝ, 0 < r ∧ ∀ n k : ℕ, 0 < n → 1 ≤ k →
    ∀ U : Edge L n k 0 → Matrices.ComplexMatrix2,
      (∀ m < k, meanIterate U m ∈ fieldsIn L n k m PeriodicLattice.complexGaugeGroup ∧
        ∀ e, Matrices.ComplexMatrix2.operatorNorm (meanIterate U m e - 1) < r) →
      Represents (meanKernelQ L n k U) ((edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
        fun B => finestMesh L k • meanCovariant U k B) ∧
      Represents (meanKernelR L n k U) ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs
        (vertexCoordinate (Vertex L n k k)) (composedCubeAverage (quietPoint U) k))
end YangMills.Construction.RunningCouplingSlope
end
