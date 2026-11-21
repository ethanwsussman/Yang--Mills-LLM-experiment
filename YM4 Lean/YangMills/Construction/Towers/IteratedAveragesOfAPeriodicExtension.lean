import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.IterMeansOfLift
open Periodisation Tower
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    1 ≤ k → ∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
      (U ∈ smallIterateFields L n k ↔
        liftGaugeField L n k 0 U ∈ Tower.FullSpace.smallIterateFields L k) ∧
      (U ∈ smallIterateFields L n k → ComplexIterLift L n k U)
end YangMills.Construction.LocalKernels.IterMeansOfLift
