import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace CubeRegions
open YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def regionInf (i : ℤ) (X Y : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ (partitionCubesIn i X ∩ partitionCubesIn i Y)
end CubeRegions
end YangMills.Construction
