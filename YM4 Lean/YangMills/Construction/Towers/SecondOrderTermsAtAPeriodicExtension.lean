import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels
def QuadraticTermsFormedAtLift : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k m : ℕ, 0 < m →
    1 ≤ k → ∀ U ∈ Tower.fieldsIn L m k 0 PeriodicLattice.complexGaugeGroup,
      U ∈ Tower.smallIterateFields L m k → Periodisation.QuadraticTermsFormed L m k U
end YangMills.Construction.LocalKernels
