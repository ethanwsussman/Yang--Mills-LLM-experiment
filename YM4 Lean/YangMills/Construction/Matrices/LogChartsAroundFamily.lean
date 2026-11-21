import YangMills.Construction.Matrices.LogChartRadius
import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.LogChartsAroundFamily
open ComplexMatrix2
variable {ι : Type} [Finite ι]
def IsChartCentre (V : ι → ComplexMatrix2) (r : ℝ) : Prop :=
  V ∈ compactProduct (fun _ : ι => FactorKind.group) ∧ 0 < r ∧ r ≤ logChartRadius
def chartNeighbourhood (r : ℝ) (V : ι → ComplexMatrix2) : Set (ι → ComplexMatrix2) :=
  {W | W ∈ complexifiedProduct (fun _ : ι => FactorKind.group) ∧
    ∀ b, operatorNorm (W b * (V b)⁻¹ - 1) < r}
def chartLog (V W : ι → ComplexMatrix2) : ι → ComplexMatrix2 :=
  fun b => Complex.I⁻¹ • logSeries (W b * (V b)⁻¹)
end YangMills.Construction.Matrices.LogChartsAroundFamily
