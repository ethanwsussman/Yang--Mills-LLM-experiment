import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.OneStepObjects
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def DoubleBlockBondCounts : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    Finite (SiteAtLevel L m K n) ∧
    (∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      {b : BondAtLevel L m K n | b ∈ (doubleBlockSymmetricSet c).bonds ∧ b.IsPositivelyOriented}.encard ≤
        ((8 * L ^ 4 : ℕ) : ℕ∞)) ∧
    ∀ b : BondAtLevel L m K n,
      {c : BondAtLevel L m K (n + 1) | c.IsPositivelyOriented ∧ b ∈ (doubleBlockSymmetricSet c).bonds}.encard ≤ 8
end YangMills.Construction.PeriodicLattice
