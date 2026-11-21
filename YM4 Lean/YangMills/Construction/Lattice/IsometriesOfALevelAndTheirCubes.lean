import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Lattice.SequencesAtACubeSizeAndAGap
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace PeriodicLattice
variable {L m : ℕ}
def IsDistanceIsometry (f : FourTorus L m → FourTorus L m) : Prop :=
  (∀ x y, torusSupNorm (f x - f y) = torusSupNorm (x - y)) ∨
  (∀ x y, torusL1Norm (f x - f y) = torusL1Norm (x - y)) ∨
  (∀ x y, torusEuclidNorm (f x - f y) = torusEuclidNorm (x - y))
def PreservesPartitionCubes (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop :=
  ∀ Q ∈ standardCubePartition L m i, σ '' Q ∈ standardCubePartition L m i
def LevelIsometryProperties : Prop :=
  ∀ (L m K t u : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K → t ≤ K →
    (u : ℤ) ≤ (m : ℤ) + levelDepth K t →
    toLevelUnits L K t (meshSize L (levelDepth K t)) = RegionChains.meshAtLevel L t t ∧
    toLevelUnits L K t (meshSize L (scaledCubeIndex K t u)) =
      (L : ℝ) ^ u * RegionChains.meshAtLevel L t t ∧
    -(m : ℤ) ≤ scaledCubeIndex K t u ∧
    (∀ f : FourTorus L m → FourTorus L m, IsDistanceIsometry f →
      f '' (sublattice L m (levelDepth K t) : Set (FourTorus L m)) = sublattice L m (levelDepth K t) →
      ∃ σ ∈ latticeIsometries L m (levelDepth K t), ⇑σ = f) ∧
    ∀ σ ∈ latticeIsometries L m (levelDepth K t),
      (PreservesPartitionCubes σ (scaledCubeIndex K t u) ↔
        σ ∈ latticeIsometries L m (scaledCubeIndex K t u)) ∧
      (PreservesPartitionCubes σ (scaledCubeIndex K t u) →
        ∀ n p : ℕ, n ≤ t → L ^ p ≤ L ^ u → PreservesPartitionCubes σ (scaledCubeIndex K n p))
end PeriodicLattice
end YangMills.Construction
