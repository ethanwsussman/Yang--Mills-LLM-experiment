import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
open InfiniteLattice (AmbientSpace)
def SymbolNormBound : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T → ∀ κ : AmbientSpace,
      quotOpNorm I I' (quotSymbol I I' T (toComplexVec κ)) ≤ kernelOpNorm I I' T
end PeriodicOperators
end YangMills.Construction
end
