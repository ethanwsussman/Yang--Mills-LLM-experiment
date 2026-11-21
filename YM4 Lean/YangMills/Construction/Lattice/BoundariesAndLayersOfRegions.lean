import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def EndpointsIn (X : Set (FourTorus L m)) (b : Bond L m j) : Prop :=
  (b.source : FourTorus L m) ∈ X ∧ (b.target : FourTorus L m) ∈ X
theorem mem_iff_exists_partitionCube {i : ℤ} {X : Set (FourTorus L m)}
    (hX : IsPartitionRegion i X) (x : FourTorus L m) :
    x ∈ X ↔ ∃ Q ∈ partitionCubesIn i X, x ∈ Q := by
  obtain ⟨C, hC, rfl⟩ := hX
  constructor
  · rintro ⟨Q, hQ, hx⟩
    exact ⟨Q, ⟨hC hQ, subset_sUnion_of_mem hQ⟩, hx⟩
  · rintro ⟨Q, hQ, hx⟩
    exact hQ.2 hx
def layerNeighborhood (i : ℤ) (Y : Set (FourTorus L m)) (a : ℤ) : Set (FourTorus L m) :=
  layerEnlargement i (cubeHull i Y) (a - 1)
end YangMills.Construction.PeriodicLattice
