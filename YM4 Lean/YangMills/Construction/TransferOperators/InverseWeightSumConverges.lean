import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def WeightDecaySum.Statement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J], WeightDecaySumFinite J
end YangMills.Construction.SpinHarmonics
end
