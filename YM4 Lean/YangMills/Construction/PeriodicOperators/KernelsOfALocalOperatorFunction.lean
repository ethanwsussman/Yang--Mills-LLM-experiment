import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpFunKernels
section Component
variable (I I' : PeriodicData)
def IsComponentKernel (q : Fin 4 → ℂ) (Y : I'.Carrier → I.Carrier → ℂ)
    (A : (Fin 4 → ℂ) → QuotHom I I') : Prop :=
  IsPhaseCovariant I I' q Y ∧
    IsFiniteRangeAllRates I I' (dephasedKernel I I' q Y) ∧
    A = symbolHom I I' (dephasedKernel I I' q Y)
end Component
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
      IsFiniteRangeAllRates I I' (coeffZero F I I' T) ∧
        ∀ (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ),
          ActionTripleUnique F I I' T p εPlus εMinus ∧
            IsComponentKernel I I' p (coeffOne F I I' T (blochWave F p εPlus))
              (jetAlong F I I' T p εPlus εMinus).f10 ∧
            IsComponentKernel I I' (-p) (coeffOne F I I' T (blochWave F (-p) εMinus))
              (jetAlong F I I' T p εPlus εMinus).f01 ∧
            IsComponentKernel I I' 0
              (coeffTwo F I I' T (blochWave F p εPlus) (blochWave F (-p) εMinus))
              (jetAlong F I I' T p εPlus εMinus).f11
end YangMills.Construction.PeriodicOperators.OpFunKernels
end
