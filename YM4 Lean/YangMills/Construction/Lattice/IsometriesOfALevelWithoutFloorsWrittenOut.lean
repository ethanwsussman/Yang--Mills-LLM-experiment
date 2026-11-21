import YangMills.Construction.Lattice.IsometriesOfALevelAndTheirCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def PermutesCubes (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  BijOn (fun κ : Set (FourTorus L m) => σ '' κ) (standardCubePartition L m i)
    (standardCubePartition L m i)
def LevelIsometryPropertiesExpanded : Prop :=
  LevelIsometryProperties ∧
  ∀ (L m K t u : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K → t ≤ K →
    (u : ℤ) ≤ (m : ℤ) + levelDepth K t →
    RegionChains.meshAtLevel L t t = 1 ∧
    (∀ f : FourTorus L m → FourTorus L m, IsDistanceIsometry f →
      f '' (sublattice L m (levelDepth K t) : Set (FourTorus L m)) = sublattice L m (levelDepth K t) →
      ∃ σ ∈ latticeIsometries L m (levelDepth K t), ⇑σ = f) ∧
    (∀ σ ∈ latticeIsometries L m (levelDepth K t),
      (σ ∈ latticeIsometries L m (scaledCubeIndex K t u) →
        PermutesCubes σ (scaledCubeIndex K t u)) ∧
      (σ '' cubeAround (0 : Site L m (scaledCubeIndex K t u)) ∈
          standardCubePartition L m (scaledCubeIndex K t u) →
        σ ∈ latticeIsometries L m (scaledCubeIndex K t u))) ∧
    ∀ σ ∈ latticeIsometries L m (scaledCubeIndex K t u), ∀ n ν : ℕ, n ≤ t → ν ≤ u →
      n ≤ K ∧ (ν : ℤ) ≤ (m : ℤ) + levelDepth K n ∧ PermutesCubes σ (scaledCubeIndex K n ν)
end YangMills.Construction.PeriodicLattice
