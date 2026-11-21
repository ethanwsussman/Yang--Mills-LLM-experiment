import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.SmallIterates
open YangMills.Construction.Tower
def SmallIteratesInComplexGaugeGroup : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n → 1 ≤ k →
    ∀ U ∈ smallIterateFields L n k, ∀ j ≤ k,
      PeriodicLattice.complexBlockFieldAtLevel j U ∈
        fieldsIn L n k j PeriodicLattice.complexGaugeGroup
end YangMills.Construction.LocalKernels.SmallIterates
end
