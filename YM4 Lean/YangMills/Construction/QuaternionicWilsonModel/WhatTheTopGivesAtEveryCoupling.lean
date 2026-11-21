import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfTheMainStatement
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.ModelSeams
def IsNonGaussianOnSmoothQuadruple (σ : SeparatedTuples.TupleFunctional) : Prop :=
  ∃ Y : TestSpaces.SepTupleOfCard 4, (∀ i, ContDiff ℝ ∞ (Y.1 i)) ∧ LimitTheorem.connectedFn σ Y ≠ 0
end YangMills.Construction.ModelSeams
end
