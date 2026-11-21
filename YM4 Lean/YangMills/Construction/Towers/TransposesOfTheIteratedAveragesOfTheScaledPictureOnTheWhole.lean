import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower.FullSpace
open YangMills.Construction.Tower.RescaledConditions (TransposeKernelScaling GeneralRelations
  AverageTransposes CoreRelations SaddleScaling TrivialRelations)
namespace IterTransposesOnFullSpace
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ Tower.FullSpace.smallIterateFields L k,
      AverageTransposes L k (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k 0))
        (Tower.FullSpace.edgePauliCoordinates L k 0)
        (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k k)) (Tower.FullSpace.edgePauliCoordinates L k k)
        (Tower.FullSpace.rescaledOperators L k U)
        (Tower.FullSpace.iterCovariantDeriv L k U k) (Tower.FullSpace.iterAdjointCubeAverage L k U k)
end IterTransposesOnFullSpace
end Tower.FullSpace
end YangMills.Construction
end
