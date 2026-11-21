import YangMills.Construction.Towers.FunctionsOfTwoSidesAndTheirMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.CoboundaryRestrictionPeriodicity
open OneStepChart
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k : ℕ, 0 < m →
    (∀ j, j ≤ k → PeriodicOperator (vertexFunctions L m k j) (edgeForms L m k j)
      FullSpace.vertexCoboundary Tower.vertexCoboundary) ∧
    (∀ j, j ≤ k → PeriodicOperator (edgeForms L m k j) (faceFunctions L m k j)
      FullSpace.edgeCoboundary Tower.edgeCoboundary) ∧
    ∀ i j, i ≤ j → j ≤ k → PeriodicOperator (vertexFunctions L m k i) (vertexFunctions L m k j)
      (FullSpace.restrictVertexFunction (Tower.meshAt L k j)) (Tower.restrictVertexFunction j)
end YangMills.Construction.Tower.UnitScale.CoboundaryRestrictionPeriodicity
end
