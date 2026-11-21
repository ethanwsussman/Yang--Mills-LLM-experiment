import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.SupDistanceLatticesCubesBlocksAndComplements
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice SupDistance
namespace CubePartitions
variable {L m : ℕ}
def IsAdmissibleUnit (L K : ℕ) (c : ℝ) : Prop :=
  c = 1 ∨ ∃ k ≤ K, c = toLevelUnits L K k 1
def supInterior (c : ℝ) (A : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ {O | IsSupOpen c O ∧ O ⊆ A}
def supClosure (c : ℝ) (A : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋂₀ {F | IsSupOpen c Fᶜ ∧ A ⊆ F}
def SupTendsto (c : ℝ) (u : ℕ → FourTorus L m) (p : FourTorus L m) : Prop :=
  Tendsto (fun n => supDistScaled c (u n) p) atTop (𝓝 0)
def infSupDist (c : ℝ) (x : FourTorus L m) (X : Set (FourTorus L m)) : ℝ≥0∞ :=
  ENNReal.ofReal c * setSupDist ({x} : Set (FourTorus L m)) X
def sitesPerAxis (L m : ℕ) (i : ℤ) : ℝ := 2 * (L : ℝ) ^ ((m : ℤ) + i)
def LatticeAndCubeCounts (L m : ℕ) (c : ℝ) (i : ℤ) : Prop :=
  (Nat.card (Site L m i) : ℝ) = sitesPerAxis L m i ^ 4 ∧
  (∀ (y : Site L m i) (μ : Fin 4),
    ((range fun k : ℤ => y + k • unitStep L m i μ).ncard : ℝ) = sitesPerAxis L m i) ∧
  Finite (Bond L m i) ∧
  Finite (Plaquette L m i) ∧
  BijOn (cubeAround : Site L m i → Set (FourTorus L m)) univ (standardCubePartition L m i) ∧
  (standardCubePartition L m i).Finite ∧
  (∀ (y : Site L m i) (μ : Fin 4),
    ((range fun k : ℤ => cubeAround (y + k • unitStep L m i μ)).ncard : ℝ) = sitesPerAxis L m i) ∧
  c * torusSide L m = sitesPerAxis L m i * (c * meshSize L i)
def CubePointsAndInteriors (L m : ℕ) (c : ℝ) (i : ℤ) : Prop :=
  (∀ (y : Site L m i), ∀ p ∈ cubeAround y, ∃ u : ℕ → FourTorus L m,
    (∀ n, supDistScaled c (u n) (y : FourTorus L m) < 1 / 2 * (c * meshSize L i)) ∧
      SupTendsto c u p) ∧
  (∀ C ⊆ standardCubePartition L m i, ∀ x ∈ supInterior c (⋃₀ C),
    ∀ Q ∈ standardCubePartition L m i, Q ∉ C → x ∉ Q) ∧
  (∀ C ⊆ standardCubePartition L m i, ∀ C' ⊆ standardCubePartition L m i, Disjoint C C' →
    Disjoint (supInterior c (⋃₀ C)) (supInterior c (⋃₀ C')))
def SubsetInteriorOfMeetingCubes (L m : ℕ) (c : ℝ) (i : ℤ) : Prop :=
  ∀ X : Set (FourTorus L m),
    X ⊆ supInterior c (⋃₀ {Q | Q ∈ standardCubePartition L m i ∧ CubeIntersects Q X})
def FinerCubeSubsetOfUnion (L m : ℕ) (i : ℤ) : Prop :=
  ∀ i' : ℤ, i ≤ i' → ∀ C ⊆ standardCubePartition L m i, ∀ y' : Site L m i',
    (y' : FourTorus L m) ∈ ⋃₀ C → ∃ Q ∈ C, cubeAround y' ⊆ Q
def EnlargementEqNeighborhood (L m : ℕ) (c : ℝ) (i : ℤ) : Prop :=
  ∀ X : Set (FourTorus L m), IsPartitionRegion i X → ∀ n : ℕ,
    {x | infSupDist c x X ≤ ENNReal.ofReal ((n : ℝ) * (c * meshSize L i))} =
      layerEnlargement i X (n : ℤ)
def ClosureDiffRegions (L m : ℕ) (c : ℝ) (i : ℤ) : Prop :=
  ∀ X X' : Set (FourTorus L m), IsPartitionRegion i X → IsPartitionRegion i X' →
    supClosure c (X \ X') = ⋃₀ (partitionCubesIn i X \ partitionCubesIn i X')
def CubePartitionFacts : Prop :=
  ∀ (s : Conventions.StandingParameters) (i : ℤ), -((s.m : ℕ) : ℤ) ≤ i →
    ∀ c : ℝ, IsAdmissibleUnit s.L s.K c →
      LatticeAndCubeCounts s.L s.m c i ∧
      CubePointsAndInteriors s.L s.m c i ∧
      SubsetInteriorOfMeetingCubes s.L s.m c i ∧
      FinerCubeSubsetOfUnion s.L s.m i ∧
      EnlargementEqNeighborhood s.L s.m c i ∧
      ClosureDiffRegions s.L s.m c i
end CubePartitions
end YangMills.Construction
end
