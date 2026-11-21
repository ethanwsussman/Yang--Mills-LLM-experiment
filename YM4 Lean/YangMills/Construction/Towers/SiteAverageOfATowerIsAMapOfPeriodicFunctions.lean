import YangMills.Construction.Towers.FunctionsOfTwoSidesAndTheirMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale
open OneStepChart
def VertexSmoothingIsPeriodic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k n : ℕ, 0 < m → n < k →
    PeriodicOperator (vertexFunctions L m k n) (vertexFunctions L m k (n + 1))
      (Tower.FullSpace.vertexSmoothing L) (Tower.vertexSmoothing L m k n)
end YangMills.Construction.Tower.UnitScale
end
