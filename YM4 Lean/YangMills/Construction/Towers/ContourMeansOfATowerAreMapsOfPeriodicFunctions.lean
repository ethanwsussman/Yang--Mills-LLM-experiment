import YangMills.Construction.Towers.FunctionsOfTwoSidesAndTheirMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.ContourAveragesPeriodic
open OneStepChart
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k j : ℕ, 0 < m → j < k →
    PeriodicOperator (edgeForms L m k j) (vertexFunctions L m k (j + 1))
      (FullSpace.cubeContourAverage L) (Tower.cubeContourAverage L m k j) ∧
    PeriodicOperator (edgeForms L m k j) (fineOnlyVertexFunctions L m k j)
      (FullSpace.fineOnlyContourAverage L (a := Tower.meshAt L k (j + 1)) (a' := Tower.meshAt L k j))
      (Tower.fineOnlyContourAverage L m k j)
end YangMills.Construction.Tower.UnitScale.ContourAveragesPeriodic
end
