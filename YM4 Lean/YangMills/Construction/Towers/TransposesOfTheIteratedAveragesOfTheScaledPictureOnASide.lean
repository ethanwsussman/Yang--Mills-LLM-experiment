import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
open RescaledConditions
namespace IterTransposesOnTorus
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ U ∈ smallIterateFields L n k,
      AverageTransposes L k (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0)
        (vertexCoordinate (Vertex L n k k)) (edgePauliCoordinates L n k k) (rescaledOperators L n k U)
        (iterCovariantDeriv L n k U k) (iterAdjointCubeAverage L n k U k)
end IterTransposesOnTorus
end Tower
end YangMills.Construction
end
