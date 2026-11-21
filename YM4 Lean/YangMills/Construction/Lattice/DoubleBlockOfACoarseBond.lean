import YangMills.Construction.Lattice.BondFunctionsAndConstraintMapOnADoubleBlock
import YangMills.Construction.Lattice.OneStepObjects
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K k : ℕ}
structure CoarseBondDoubleBlock (c : BondAtLevel L m K (k + 1)) : Prop where
  encard_positive_le :
    {b : BondAtLevel L m K k | b ∈ (doubleBlockSymmetricSet c).bonds ∧ b.IsPositivelyOriented}.encard ≤
      ((8 * L ^ 4 : ℕ) : ℕ∞)
  pivot_isPositivelyOriented : (pivot c : BondAtLevel L m K k).IsPositivelyOriented
  pivot_mem : (pivot c : BondAtLevel L m K k) ∈ (doubleBlockSymmetricSet c).bonds
  eq_or_eq_opposite_of_pivot_mem : ∀ c' : BondAtLevel L m K (k + 1),
    (pivot c' : BondAtLevel L m K k) ∈ (doubleBlockSymmetricSet c).bonds →
      c' = c ∨ c' = c.opposite
  ne_pivot_of_mem_unitBlock : ∀ (b : BondAtLevel L m K k) (y : SiteAtLevel L m K (k + 1)),
    (b.source : FourTorus L m) ∈ unitBlock y → (b.target : FourTorus L m) ∈ unitBlock y →
      ∀ c' : BondAtLevel L m K (k + 1), b ≠ pivot c'
def CoarseBondDoubleBlock.Statement : Prop :=
  ∀ (L m K k : ℕ) (c : BondAtLevel L m K (k + 1)) (μ : Fin 4),
    IsCoarseBondSetup c μ → CoarseBondDoubleBlock c
end PeriodicLattice
end YangMills.Construction
