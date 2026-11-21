import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.PolydiscOfTheOneStepObjects
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def HolomorphyOfBoundedStepQuantities : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ r : ℝ, 0 < r → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented →
      (∀ a₀ a : LieBondField (doubleBlockSymmetricSet c), supOperatorNorm a₀ < r →
        supOperatorNorm a < r → PolydiscBounds s c a₀ a) →
      IsHolomorphicOnPolydisc r s c
end YangMills.Construction.PeriodicLattice
end
