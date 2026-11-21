import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels
open Periodisation
def QuadraticKernelAtExtensionDescends : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    1 ≤ k → ∀ U ∈ Tower.fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
      U ∈ Tower.smallIterateFields L n k → ∀ μ ∈ Tower.complexEdgeForms L n k k,
        QuadraticKernelDescends L n k U μ
end YangMills.Construction.LocalKernels
