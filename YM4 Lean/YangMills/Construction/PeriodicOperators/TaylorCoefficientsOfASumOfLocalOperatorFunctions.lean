import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
def CoeffAdditivity.Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ,
      IsLocalOpFun F I I' T → IsLocalOpFun F I I' T' →
      ∀ ζ ζ' : F.Carrier → ℂ,
        coeffOne F I I' (opFunAdd T T') ζ =
            coeffOne F I I' T ζ + coeffOne F I I' T' ζ ∧
          coeffTwo F I I' (opFunAdd T T') ζ ζ' =
            coeffTwo F I I' T ζ ζ' + coeffTwo F I I' T' ζ ζ'
end YangMills.Construction.PeriodicOperators
end
