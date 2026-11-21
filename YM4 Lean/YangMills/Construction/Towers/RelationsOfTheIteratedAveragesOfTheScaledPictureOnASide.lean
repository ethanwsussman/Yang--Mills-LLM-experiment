import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def RescaledIterRelations : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ U ∈ Tower.smallIterateFields L n k,
      Tower.RescaledConditions.CoreRelations (Tower.vertexCoordinate (Tower.Vertex L n k 0))
        (Tower.edgePauliCoordinates L n k 0)
        (Tower.vertexCoordinate (Tower.Vertex L n k k)) (Tower.edgePauliCoordinates L n k k)
        (Tower.rescaledOperators L n k U)
        (Tower.covDiff U) (Tower.iterCovariantDeriv L n k U k)
        (Tower.iterAdjointCubeAverage L n k U k)
        (Tower.covDiff (PeriodicLattice.complexBlockFieldAtLevel k U))
        (Tower.covDiffKernel L n k k (PeriodicLattice.complexBlockFieldAtLevel k U))
        (Tower.backgroundForm L n k U)
end Tower
end YangMills.Construction
end
