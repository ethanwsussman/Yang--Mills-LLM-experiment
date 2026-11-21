import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpFunAdd
def LocalClosed : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ,
      IsLocalOpFun F I I' T → IsLocalOpFun F I I' T' →
        IsLocalOpFun F I I' (opFunAdd T T')
end YangMills.Construction.PeriodicOperators.OpFunAdd
end
