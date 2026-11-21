import YangMills.Construction.Towers.FunctionsOfTwoSidesAndTheirMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.FineOnlyVertexCoordinates
open OneStepChart
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k j : ℕ, 0 < m → j < k →
    Nonempty (CellCoordinates (2 * L ^ m) (fineOnlyVertexFunctions L m k j))
end YangMills.Construction.Tower.UnitScale.FineOnlyVertexCoordinates
end
