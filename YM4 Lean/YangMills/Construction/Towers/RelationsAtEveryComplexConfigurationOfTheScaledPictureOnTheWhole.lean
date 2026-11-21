import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FullSpace
namespace ComplexFieldRescaledRelations
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
      RescaledConditions.GeneralRelations (Tower.vertexCoordinate (FullSpace.Vertex L k 0))
        (FullSpace.edgePauliCoordinates L k 0) (FullSpace.rescaledOperators L k U) (FullSpace.covDiff U)
        (FullSpace.complexHessianOperator U)
end ComplexFieldRescaledRelations
end FullSpace
end Tower
end YangMills.Construction
end
