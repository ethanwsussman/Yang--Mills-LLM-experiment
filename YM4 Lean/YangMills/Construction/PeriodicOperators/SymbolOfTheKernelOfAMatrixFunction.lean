import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace MatFunKernelSymbol
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' → ∀ υ : ℝ, 0 < υ →
    ∀ M : (Fin 4 → ℂ) → QuotHom I I', IsHolomorphicNbhd (imStrip υ) M →
      QuotHomFamilyBoundedOn (imStrip υ) M → IsQuasiPeriodic (imStrip υ) M →
        ∀ κ ∈ openImStrip υ,
          SymbolSummableAt I I' (matFunKernel I I' M) κ ∧
            ∀ j i, fourierSymbol I I' (matFunKernel I I' M) κ j i = carrierEntry (M κ) j i
end MatFunKernelSymbol
end YangMills.Construction.PeriodicOperators
end
