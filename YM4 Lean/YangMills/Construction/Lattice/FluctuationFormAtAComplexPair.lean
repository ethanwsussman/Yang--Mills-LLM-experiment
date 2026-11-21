import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ComplexPairFluctuation
open YangMills.Construction.Matrices
variable {L m K k : ℕ}
def formsSupportedOn (Y : Set (BondAtLevel L m K k)) : Set (BondAtLevel L m K k → ComplexMatrix2) :=
  {A | IsBondForm complexLieAlgebra A ∧
    ∀ b : BondAtLevel L m K k, b.IsPositivelyOriented → b ∉ Y → A b = 0}
end YangMills.Construction.PeriodicLattice.ComplexPairFluctuation
