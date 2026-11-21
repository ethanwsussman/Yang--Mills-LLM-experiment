import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
namespace RealKernels
open Quotients (conjKernel)
def Claim : Prop :=
  ∀ I J : PeriodicData, IsPeriodic I → IsPeriodic J →
    ∀ M : (Fin 4 → ℂ) → QuotHom I J, QuotHomFamilyContinuousOn (n := 4) realDualPoints M →
      (∀ κ ∈ realDualPoints, conjKernel (linearMapEntry (M κ)) = linearMapEntry (M (-star κ))) →
        ∀ j i, (matFunKernel I J M j i).im = 0
end RealKernels
end PeriodicOperators
end YangMills.Construction
end
