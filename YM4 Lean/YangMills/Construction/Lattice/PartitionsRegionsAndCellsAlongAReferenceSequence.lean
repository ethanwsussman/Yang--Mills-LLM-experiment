import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice
namespace CellRegions
variable {L m : ℕ}
def cellPartition (L m K : ℕ) : Set (Set (FourTorus L m)) := standardCubePartition L m (K : ℤ)
def IsAdmissibleRegion (K : ℕ) (X : Set (FourTorus L m)) : Prop :=
  ∃ i : ℤ, -(m : ℤ) ≤ i ∧ i ≤ K ∧ IsPartitionRegion i X
def cellsIn (K : ℕ) (A : Set (FourTorus L m)) : Set (Set (FourTorus L m)) :=
  {q | q ∈ cellPartition L m K ∧ q ⊆ A}
def cellInf (K : ℕ) (A B : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ (cellsIn K A ∩ cellsIn K B)
end CellRegions
end YangMills.Construction
end
