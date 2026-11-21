import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LeibnizRule
def Claim : Prop :=
  ∀ F I I' I'' : PeriodicData, IsPeriodic F → IsPeriodic I →
    IsPeriodic I' → IsPeriodic I'' →
    ∀ (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (S : (F.Carrier → ℂ) → I.Carrier → I''.Carrier → ℂ),
      IsLocalOpFun F I I' T → IsLocalOpFun F I'' I S →
      ∀ ζ ζ' : F.Carrier → ℂ,
        coeffOne F I'' I' (opFunComp T S) ζ =
            compKernel (coeffOne F I I' T ζ) (coeffZero F I'' I S) +
              compKernel (coeffZero F I I' T) (coeffOne F I'' I S ζ) ∧
          coeffTwo F I'' I' (opFunComp T S) ζ ζ' =
            compKernel (coeffTwo F I I' T ζ ζ') (coeffZero F I'' I S) +
              compKernel (coeffZero F I I' T) (coeffTwo F I'' I S ζ ζ') +
              compKernel (coeffOne F I I' T ζ) (coeffOne F I'' I S ζ') +
              compKernel (coeffOne F I I' T ζ') (coeffOne F I'' I S ζ)
end YangMills.Construction.PeriodicOperators.LeibnizRule
end
