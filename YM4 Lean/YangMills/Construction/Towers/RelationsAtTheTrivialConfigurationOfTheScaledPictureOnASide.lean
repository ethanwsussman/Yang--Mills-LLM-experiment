import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace TrivialFieldRescaledRelations
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    RescaledConditions.TrivialRelations (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0)
      (vertexCoordinate (Vertex L n k k)) (edgePauliCoordinates L n k k) (vertexCoordinate (Face L n k 0))
      (rescaledOperators L n k (trivialField L n k 0)) scaledVertexCoboundary
      scaledEdgeCoboundary scaledVertexCoboundary (crossingSmoothingIter L n k k)
      (vertexSmoothingIter L n k k)
end TrivialFieldRescaledRelations
end Tower
end YangMills.Construction
end
