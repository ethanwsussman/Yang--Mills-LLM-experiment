import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpenStripInverse
def Claim : Prop :=
  ∀ I : PeriodicData, IsPeriodic I → ∀ υ : ℝ, 0 < υ → ∀ T : I.Carrier → I.Carrier → ℂ,
    IsPeriodicKernel I I T → SymbolSummableOn I I T (openImStrip υ) →
    QuotHomFamilyHolomorphicOn (n := 4) (openImStrip υ) (symbolHom I I T) →
    (∀ κ ∈ openImStrip υ, IsInvertibleQuotHom (symbolHom I I T κ)) →
      SymbolInvertibleOnReals I T ∧
        IsPeriodicKernel I I (periodicInverse I T) ∧
        (∀ j i, CompSummableAt (periodicInverse I T) T j i) ∧
        (∀ j i, CompSummableAt T (periodicInverse I T) j i) ∧
        compKernel (periodicInverse I T) T = idKernel I ∧
        compKernel T (periodicInverse I T) = idKernel I ∧
        SymbolSummableOn I I (periodicInverse I T) (openImStrip υ) ∧
        ∀ κ ∈ openImStrip υ, symbolHom I I (periodicInverse I T) κ =
          quotHomInverse (symbolHom I I T κ)
end YangMills.Construction.PeriodicOperators.OpenStripInverse
end
