import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
namespace SymbolKernel
def KernelOfSymbol : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T →
      matFunKernel I I' (symbolHom I I' T) = T
end SymbolKernel
end PeriodicOperators
end YangMills.Construction
end
