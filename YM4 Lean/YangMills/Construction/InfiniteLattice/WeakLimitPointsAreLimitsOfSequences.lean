import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions
def IsLiftedMeasureAtSide (L K : ℕ) (β ℓ' : ℝ)
    (ρ : RealWeakState (PeriodicLattice.meshSize L (K : ℤ))) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ℓ' = PeriodicLattice.torusSide L m ∧ ρ.measure = liftedWilsonMeasure L m K β
def IsLimitAlongSideSequence (L K : ℕ) (β : ℝ) (ℓ : ℕ → ℝ)
    (ρ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ)))
    (ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ))) : Prop :=
  SidesTendToInfinity L ℓ ∧ (∀ i, 1 ≤ i → IsLiftedMeasureAtSide L K β (ℓ i) (ρ i)) ∧
    RealWeakState.TendstoWeakly ρ ν
def SequentialLimitCharacterization : Prop :=
  ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K → ∀ β : ℝ, 0 < β →
    ∀ ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
      (IsLimitOfLiftedMeasures L K β ν ↔ ∃ ℓ ρ, IsLimitAlongSideSequence L K β ℓ ρ ν) ∧
      (IsLimitOfLiftedMeasures L K β ν →
        ∃ ℓ ρ, IsLimitAlongSideSequence L K β ℓ ρ ν ∧ ∀ i, 1 ≤ i → ℓ i < ℓ (i + 1))
end YangMills.Construction.InfiniteLattice.PeriodicExtensions
