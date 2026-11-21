import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConditionalMeansOnBoxes
open YangMills.Construction.InfiniteLattice
variable {a : ℝ}
abbrev IntegerPoint : Type := Fin 4 → ℤ
def latticePointOf (a : ℝ) (n : IntegerPoint) : LatticePoint a := ⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩
end YangMills.Construction.ConditionalMeansOnBoxes
end
