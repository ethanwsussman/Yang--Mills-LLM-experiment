import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IteratedDriftKernel
open PeriodicOperators
def DriftKernelRepresents : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ smallIterateFields L k,
      Represents
        ((edgePauliCoordinates L k 0).kernel (vertexCoordinate (Vertex L k k)) (iterContourLogDrift L k U k))
        (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0) (vertexCoordinate (Vertex L k k))
          (iterContourLogDrift L k U k))
end YangMills.Construction.Tower.FullSpace.IteratedDriftKernel
end
