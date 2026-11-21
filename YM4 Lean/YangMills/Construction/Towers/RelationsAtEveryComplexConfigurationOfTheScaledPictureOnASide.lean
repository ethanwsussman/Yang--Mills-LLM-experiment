import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
open RescaledConditions
namespace ComplexFieldRescaledRelations
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
      GeneralRelations (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0)
        (rescaledOperators L n k U) (covDiff U) (complexHessianOperator U)
end ComplexFieldRescaledRelations
end Tower
end YangMills.Construction
end
