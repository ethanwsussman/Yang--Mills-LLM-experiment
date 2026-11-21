import YangMills.Construction.Geometry.TorusCubes
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.LevelUnitCharts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric Conventions
namespace PeriodicLattice
def halfIntegerFaces (a : ℝ) : Set ℝ := {x | ∃ n : ℤ, x = a * ((n : ℝ) + 1 / 2)}
def CubeFactsInUnit (s : StandingParameters) (u : ℝ → ℝ)
    (p : (Fin 4 → ℝ) → FourTorus s.L s.m) (i i' : ℤ) : Prop :=
  (∀ y : Fin 4 → ℝ, (∀ ν, ∃ n : ℤ, y ν = u (meshSize s.L i) * (n : ℝ)) →
    ∃ z : Site s.L s.m i, (z : FourTorus s.L s.m) = p y ∧
      cubeAround z = p '' pi univ fun ν =>
        Icc (y ν - 1 / 2 * u (meshSize s.L i)) (y ν + 1 / 2 * u (meshSize s.L i))) ∧
  halfIntegerFaces (u (meshSize s.L i)) ⊆ halfIntegerFaces (u (meshSize s.L i')) ∧
  ∀ (t : ℝ) (f : Fin 4 → ℝ), 0 < t → t < u (torusSide s.L s.m) →
    IsPartitionRegion i (p '' TorusCubes.realCube f t) →
      (∀ ν, f ν ∈ halfIntegerFaces (u (meshSize s.L i)) ∧
        f ν + t ∈ halfIntegerFaces (u (meshSize s.L i))) ∧
      ∃ n : ℕ, 0 < n ∧ t = (n : ℝ) * u (meshSize s.L i)
def PartitionRefinement (s : StandingParameters) (i i' : ℤ) : Prop :=
  ⋃₀ standardCubePartition s.L s.m i = univ ∧
  (∀ Q ∈ standardCubePartition s.L s.m i, IsPartitionRegion i' Q) ∧
  (∀ X : Set (FourTorus s.L s.m), IsPartitionRegion i X → IsPartitionRegion i' X) ∧
  ∀ X : Set (FourTorus s.L s.m), IsPartitionRegion i X →
    ⋃₀ {Q | Q ∈ standardCubePartition s.L s.m i ∧ ¬Q ⊆ X} =
      ⋃₀ {Q | Q ∈ standardCubePartition s.L s.m i' ∧ ¬Q ⊆ X} ∧
    complementRegion i X = complementRegion i' X
def LevelUnitLengths (s : StandingParameters) (k k' : ℕ) : Prop :=
  (∀ r t : ℝ, toLevelUnits s.L s.K k' r = t →
    toLevelUnits s.L s.K k r = t * (s.L : ℝ) ^ ((k' : ℤ) - (k : ℤ))) ∧
  (∀ j : ℤ, toLevelUnits s.L s.K k (meshSize s.L j) =
    (s.L : ℝ) ^ (((s.K : ℕ) : ℤ) - (k : ℤ) - j)) ∧
  toLevelUnits s.L s.K k (meshSize s.L (levelDepth s.K k)) = 1 ∧
  toLevelUnits s.L s.K k (meshSize s.L ((s.K : ℕ) : ℤ)) = finestMeshInLevelUnits s.L k ∧
  toLevelUnits s.L s.K k (torusSide s.L s.m) =
    2 * (s.L : ℝ) ^ (((s.m : ℕ) : ℤ) + ((s.K : ℕ) : ℤ) - (k : ℤ))
def StandardPartitionsInUnits : Prop :=
  ∀ s : StandingParameters,
    (∀ i i' : ℤ, -((s.m : ℕ) : ℤ) ≤ i → i ≤ i' →
      PartitionRefinement s i i' ∧
      CubeFactsInUnit s id (torusProj (torusSide s.L s.m)) i i' ∧
      ∀ k : ℕ, k ≤ (s.K : ℕ) →
        CubeFactsInUnit s (toLevelUnits s.L s.K k) (LevelUnits.coverMap s k) i i') ∧
    ∀ k k' : ℕ, k ≤ (s.K : ℕ) → k' ≤ (s.K : ℕ) → LevelUnitLengths s k k'
end PeriodicLattice
end YangMills.Construction
