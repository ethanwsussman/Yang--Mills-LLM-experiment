import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def RescaledIterRelations : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ Tower.FullSpace.smallIterateFields L k,
      Tower.RescaledConditions.CoreRelations (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k 0))
        (Tower.FullSpace.edgePauliCoordinates L k 0)
        (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k k)) (Tower.FullSpace.edgePauliCoordinates L k k)
        (Tower.FullSpace.rescaledOperators L k U)
        (Tower.FullSpace.covDiff U) (Tower.FullSpace.iterCovariantDeriv L k U k)
        (Tower.FullSpace.iterAdjointCubeAverage L k U k)
        (Tower.FullSpace.covDiff (Tower.FullSpace.complexIter L k k U))
        (Tower.FullSpace.covDiffKernel L k k (Tower.FullSpace.complexIter L k k U))
        (Tower.FullSpace.backgroundForm L k U)
end YangMills.Construction.Tower.FullSpace
end
