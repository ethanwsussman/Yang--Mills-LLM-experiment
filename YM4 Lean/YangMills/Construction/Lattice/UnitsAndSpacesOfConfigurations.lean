import YangMills.Construction.Lattice.RegularSetsOfTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
def smallCurvatureConfigsAtLevel (L m K k : ℕ) (r : ℝ) :
    Set (BondAtLevel L m K 0 → ComplexMatrix2) :=
  smallCurvatureConfigs L m K k r
end YangMills.Construction.PeriodicLattice
