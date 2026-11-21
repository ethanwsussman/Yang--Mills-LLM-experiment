import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
namespace MatrixFunctionKernel
open TorusMetric (l1NormVec)
def DecayBound : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' → ∀ υ : ℝ, 0 < υ →
    ∀ M : (Fin 4 → ℂ) → QuotHom I I', IsHolomorphicNbhd (imStrip υ) M →
      QuotHomFamilyBoundedOn (imStrip υ) M → IsQuasiPeriodic (imStrip υ) M →
        IsPeriodicKernel I I' (matFunKernel I I' M) ∧
        ∀ j i, ‖matFunKernel I I' M j i‖ ≤
          sSup ((fun κ => ‖carrierEntry (M κ) j i‖) '' imStrip υ) *
            Real.exp (-υ * l1NormVec (I.pos i - I'.pos j))
end MatrixFunctionKernel
end PeriodicOperators
end YangMills.Construction
end
