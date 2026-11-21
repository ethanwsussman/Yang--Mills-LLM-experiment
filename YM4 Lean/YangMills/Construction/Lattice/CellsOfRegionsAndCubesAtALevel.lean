import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice
universe u
noncomputable section
namespace RegionCells
variable {L m : ℕ}
def LevelInRange (m K m' j : ℕ) : Prop := j ≤ K ∧ (m' : ℤ) ≤ (m : ℤ) + K - j
def partitionAtLevel (L m K m' j : ℕ) : Set (Set (FourTorus L m)) :=
  standardCubePartition L m (coarseCubeIndex K m' j)
end RegionCells
end
end YangMills.Construction
