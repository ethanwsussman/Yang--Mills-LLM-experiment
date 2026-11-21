import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.LevelCubesAndBlocks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def CubesUnderRefinement : Prop :=
  ∀ L m : ℕ, Odd L → 13 ≤ L → 0 < m →
    (∀ t t' : ℤ, -(m : ℤ) ≤ t → t ≤ t' →
      (∀ y : Site L m t, cubeAround y =
        ⋃ x : Site L m t', ⋃ _ : (x : FourTorus L m) ∈ refinedBlock (t' - t).toNat y,
          cubeAround x) ∧
      ⋃₀ standardCubePartition L m t = univ ∧
      (∀ X : Set (FourTorus L m), IsPartitionRegion t X → IsPartitionRegion t' X) ∧
      (∀ X : Set (FourTorus L m), IsPartitionRegion t X → ∀ z : FourTorus L m, z ∉ X →
        z ∈ complementRegion t X)) ∧
    ∀ K i j : ℕ, 0 < K → i ≤ j → j ≤ K → ∀ y : SiteAtLevel L m K j,
      cubeAtLevel y =
        ⋃ x : SiteAtLevel L m K i, ⋃ _ : (x : FourTorus L m) ∈ blockAtLevel i y, cubeAtLevel x
end YangMills.Construction.PeriodicLattice
