import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.PolydiscOfTheOneStepObjects
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def OneStepPolydiscRadiusExists : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 16 ∧
    ∀ m K n : ℕ, 0 < m → n < K →
      ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented →
      ∀ a₀ a : LieBondField (doubleBlockSymmetricSet c), supOperatorNorm a₀ < r →
        supOperatorNorm a < r → PolydiscBounds s c a₀ a
end YangMills.Construction.PeriodicLattice
end
