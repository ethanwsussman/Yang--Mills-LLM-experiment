import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ}
def trivialBondData (K : ℕ) (q : ℕ) : BondAtLevel L m K q → ComplexMatrix2 := trivialGaugeField
end YangMills.Construction.PeriodicLattice
