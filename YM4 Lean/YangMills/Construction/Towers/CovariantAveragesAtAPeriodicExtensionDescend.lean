import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.PeriodicLiftDescent
def CovariantMeansDescend : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    1 ≤ k → ∀ U ∈ Tower.fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
      U ∈ Tower.smallIterateFields L n k → Periodisation.IteratesDescend L n k U
end YangMills.Construction.LocalKernels.PeriodicLiftDescent
