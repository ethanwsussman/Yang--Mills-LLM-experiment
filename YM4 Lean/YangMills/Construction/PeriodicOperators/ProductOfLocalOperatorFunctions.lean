import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpFunComp
def LocalClosed : Prop :=
  ∀ F I I' I'' : PeriodicData, IsPeriodic F → IsPeriodic I →
    IsPeriodic I' → IsPeriodic I'' →
      ∀ (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ)
        (S : (F.Carrier → ℂ) → I.Carrier → I''.Carrier → ℂ),
        IsLocalOpFun F I I' T → IsLocalOpFun F I'' I S →
          IsLocalOpFun F I'' I' (opFunComp T S)
end YangMills.Construction.PeriodicOperators.OpFunComp
end
