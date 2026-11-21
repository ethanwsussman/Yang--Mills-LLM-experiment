import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetQuasiPeriodic
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
      ∀ (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ),
        IsQuasiPeriodic univ (jetAlong F I I' T p εPlus εMinus).f00 ∧
          IsQuasiPeriodic univ (jetAlong F I I' T p εPlus εMinus).f10 ∧
          IsQuasiPeriodic univ (jetAlong F I I' T p εPlus εMinus).f01 ∧
          IsQuasiPeriodic univ (jetAlong F I I' T p εPlus εMinus).f11
end YangMills.Construction.PeriodicOperators.JetQuasiPeriodic
end
