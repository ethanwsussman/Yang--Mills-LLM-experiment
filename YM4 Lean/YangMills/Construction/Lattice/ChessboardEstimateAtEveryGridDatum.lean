import YangMills.Construction.Lattice.ReflectionPositivityAndChessboardEstimateOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellGrid
def CheckerboardBoundAtAllGrids : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ) (β : ℝ), 0 < β → d.CheckerboardBound β
end YangMills.Construction.CellGrid
end
