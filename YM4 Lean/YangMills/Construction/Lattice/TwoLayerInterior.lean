import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def doubleLayerInteriorCubes (K m' p : ℕ) (X : Set (FourTorus L m)) : Set (Set (FourTorus L m)) :=
  {Q | -(m : ℤ) ≤ coarseCubeIndex K m' (p - 1) ∧
    Q ∈ standardCubePartition L m (coarseCubeIndex K m' (p - 1)) ∧
    layerEnlargement (coarseCubeIndex K m' (p - 1)) Q 2 ⊆ X}
def doubleLayerInterior (K m' p : ℕ) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ doubleLayerInteriorCubes K m' p X
end PeriodicLattice
end YangMills.Construction
