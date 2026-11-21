import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.TracesOfKernelsAtUnitFields
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.QuotTraceLimits
open UnitFieldTraces
def UnitFieldTracesConverge : Prop :=
  ∀ F P : PeriodicData, IsPeriodic F → IsPeriodic P →
    ∀ (T : (F.Carrier → ℂ) → P.Carrier → P.Carrier → ℂ) (ρ R₀ : ℝ), IsLocalWith F P P T ρ R₀ →
    ∀ R : P.Carrier → P.Carrier → ℂ, IsPeriodicKernel P P R →
      compKernel (coeffZero F P P T) R = idKernel P →
      compKernel R (coeffZero F P P T) = idKernel P →
      (∀ᶠ s : ℕ in atTop, IsUnit (LogDetSecondDerivs.quotOperator F P T s 0)) ∧
      ∀ κ κ' : F.Carrier,
        Tendsto (fun s : ℕ => quotTraceDefect F P T s (quotIndicator F s κ) (quotIndicator F s κ')) atTop
          (𝓝 (kernelTraceDefect F P T R (siteIndicator F κ) (siteIndicator F κ')))
end YangMills.Construction.PeriodicOperators.QuotTraceLimits
end
