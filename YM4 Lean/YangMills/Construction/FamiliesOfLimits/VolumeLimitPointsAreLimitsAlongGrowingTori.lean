import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.FamiliesOfLimits
def InfiniteVolumeLimitsAlongGrowingTori : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (sides : Set ℝ) (ℓ₀ : ℝ),
    (∀ m : ℕ, 0 < m → ℓ₀ ≤ PeriodicLattice.torusSide L m →
      PeriodicLattice.torusSide L m ∈ sides) →
    ∀ (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ)
      (ν : ∀ j, Measure (InfiniteLattice.GaugeField
        (PeriodicLattice.meshSize L (((K j : ℕ)) : ℤ)))),
      (∀ j, 0 < β j) → (∀ j, InfiniteLattice.IsInfiniteVolumeLimit L (K j) (β j) (ν j)) →
      ∃ m : ℕ+ → ℕ, (∀ j, PeriodicLattice.torusSide L (m j) ∈ sides) ∧
        Tendsto (fun j => PeriodicLattice.torusSide L (m j)) atTop atTop ∧
        ∀ (n : ℕ), 2 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n,
          (∀ᶠ j in atTop,
            SchwingerFunctions.IsR4TestFamily (PeriodicLattice.torusSide L (m j)) X.1) ∧
          Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 L (m j) (K j) (β j) X.1 -
            InfiniteLattice.smearedEnergyCumulant (ν j) X.1) atTop (𝓝 0)
end YangMills.Construction.FamiliesOfLimits
end
