import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.CovDiffAtLift
open Periodisation Tower
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ (j : ℕ) (h : j ≤ k), ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      CovDiffDescends L n k j h V
end YangMills.Construction.LocalKernels.CovDiffAtLift
