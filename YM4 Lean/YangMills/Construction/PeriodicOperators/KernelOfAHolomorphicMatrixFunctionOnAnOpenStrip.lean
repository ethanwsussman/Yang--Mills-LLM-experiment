import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpenStripHolomorphicKernel
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' → ∀ υ : ℝ, 0 < υ →
    ∀ M : (Fin 4 → ℂ) → QuotHom I I',
      QuotHomFamilyHolomorphicOn (n := 4) (openImStrip υ) M →
      (∀ υ' : ℝ, 0 < υ' → υ' < υ → QuotHomFamilyBoundedOn (imStrip υ') M) →
      IsQuasiPeriodic (openImStrip υ) M →
        realDualPoints ⊆ openImStrip υ ∧
        QuotHomFamilyContinuousOn (n := 4) (openImStrip υ) M ∧
        QuotHomFamilyContinuousOn (n := 4) realDualPoints M ∧
        IsPeriodicKernel I I' (matFunKernel I I' M) ∧
        SymbolSummableOn I I' (matFunKernel I I' M) (openImStrip υ) ∧
        ∀ κ ∈ openImStrip υ, symbolHom I I' (matFunKernel I I' M) κ = M κ
end YangMills.Construction.PeriodicOperators.OpenStripHolomorphicKernel
end
