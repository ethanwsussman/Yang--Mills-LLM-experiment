import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TransposeTaylor
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
      ∀ ζ ζ' : F.Carrier → ℂ,
        coeffOne F I' I (opFunTranspose T) ζ = kernelTranspose I I' (coeffOne F I I' T ζ) ∧
          coeffTwo F I' I (opFunTranspose T) ζ ζ' =
            kernelTranspose I I' (coeffTwo F I I' T ζ ζ')
end YangMills.Construction.PeriodicOperators.TransposeTaylor
end
