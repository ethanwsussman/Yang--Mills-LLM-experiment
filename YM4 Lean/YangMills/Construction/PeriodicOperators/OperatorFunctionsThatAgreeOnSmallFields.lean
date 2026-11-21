import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LocalAgreement
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T S : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ ζ, IsSupBelow F ζ ρ → S ζ = T ζ) →
        IsLocalOpFun F I I' S ∧
        ∀ (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ),
          jetAlong F I I' S p εPlus εMinus = jetAlong F I I' T p εPlus εMinus
end YangMills.Construction.PeriodicOperators.LocalAgreement
end
