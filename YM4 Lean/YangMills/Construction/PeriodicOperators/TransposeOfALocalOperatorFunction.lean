import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpFunTransposeLocal
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ,
      IsLocalOpFun F I I' T → IsLocalOpFun F I' I (opFunTranspose T)
end YangMills.Construction.PeriodicOperators.OpFunTransposeLocal
end
