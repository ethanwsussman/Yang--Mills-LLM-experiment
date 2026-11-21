import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def RescaledTrivialRelations : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    Tower.RescaledConditions.TrivialRelations (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k 0))
      (Tower.FullSpace.edgePauliCoordinates L k 0)
      (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k k)) (Tower.FullSpace.edgePauliCoordinates L k k)
      (Tower.vertexCoordinate (Tower.FullSpace.Face L k 0))
      (Tower.FullSpace.rescaledOperators L k fun _ => 1) Tower.FullSpace.scaledVertexCoboundary
      Tower.FullSpace.scaledEdgeCoboundary Tower.FullSpace.scaledVertexCoboundary
      (Tower.FullSpace.crossingSmoothingIter L k k)
      (Tower.FullSpace.vertexSmoothingIter L k k)
end YangMills.Construction.Tower.FullSpace
end
