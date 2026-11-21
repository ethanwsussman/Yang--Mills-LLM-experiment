import YangMills.Construction.TransferOperators.ObjectsOfAnInsertionOfContractionsBetweenLayers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
def CubicPartitionFunctionTraceStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (μ : Fin 4) (Γ : CubicPeriodSublattice), Γ.PartitionFunctionEqTrace μ β
end YangMills.Construction.TransferOperators
end
