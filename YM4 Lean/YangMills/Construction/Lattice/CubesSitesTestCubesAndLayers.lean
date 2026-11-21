import YangMills.Construction.Lattice.BoundariesAndLayersOfRegions
import YangMills.Construction.Lattice.LargeFieldOperationDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric ParameterChoice
namespace PeriodicLattice
def CoarserPartitionRefines (L m : ℕ) (i i' : ℤ) : Prop :=
  (∀ Q ∈ standardCubePartition L m i, Q = ⋃₀ partitionCubesIn i' Q) ∧
  (∀ Q' ∈ standardCubePartition L m i', ∃! Q, Q ∈ standardCubePartition L m i ∧ Q' ⊆ Q) ∧
  ∀ X : Set (FourTorus L m), IsPartitionRegion i X → IsPartitionRegion i' X
def SiteInteriorToCoarseCube (L m : ℕ) (i : ℤ) (n : ℕ) (x : Site L m (i + n)) : Prop :=
  (∀ Q ∈ standardCubePartition L m i, (x : FourTorus L m) ∉ frontier Q) ∧
  ∃ Q ∈ standardCubePartition L m i,
    ((x : FourTorus L m) ∈ Q ∧
      ∀ Q' ∈ standardCubePartition L m i, (x : FourTorus L m) ∈ Q' → Q' = Q) ∧
    Q ∈ nhds (x : FourTorus L m) ∧
    (∀ X : Set (FourTorus L m), IsPartitionRegion i X →
      ((x : FourTorus L m) ∈ X ↔ Q ∈ partitionCubesIn i X)) ∧
    cubeAround x ⊆ Q ∧
    ∀ n' : ℕ, refinedBlock n' x ⊆ Q
def BlockAverageSeesOnlyDoubleBlock (L m K k : ℕ) : Prop :=
  ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
    ∀ V ∈ gaugeFieldsAtLevel L m K k, ∀ V' ∈ gaugeFieldsAtLevel L m K k,
      (∀ b : BondAtLevel L m K k, EndpointsIn (bondDoubleBlock c) b → V b = V' b) →
        blockAverage (Averaging.smoothingRadius L) V c =
          blockAverage (Averaging.smoothingRadius L) V' c
def SubordinateToCoarsePartition (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ)
    (k : ℕ) (F : Set (Set (FourTorus c.L m))) : Prop :=
  (∀ Q ∈ F, ∃! Q', Q' ∈ (CubesOfStep.coarsePartition c K x k : Set (Set (FourTorus c.L m))) ∧
    Q ⊆ Q') ∧
  ∀ X : Set (FourTorus c.L m), IsPartitionRegion (CubesOfStep.coarsePartitionIndex c K x k) X →
    ∃ C ⊆ F, X = ⋃₀ C
def TestPartitionSubordinate (c : ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    Prop :=
  SubordinateToCoarsePartition (m := m) c K x k (CubesOfStep.testPartition c K x k) ∧
  (CubesOfStep.densityPartition c K x (k + 1) : Set (Set (FourTorus c.L m))) =
    CubesOfStep.testPartition c K x k ∧
  SubordinateToCoarsePartition (m := m) c K x k (CubesOfStep.densityPartition c K x (k + 1))
def LayerNeighborhoodCharacterization (L m : ℕ) (i : ℤ) (Y : Set (FourTorus L m)) (a : ℕ) :
    Prop :=
  (∀ Q ∈ standardCubePartition L m i, Q ∈ partitionCubesIn i (layerNeighborhood i Y (a : ℤ)) ↔
    setSupDist Q Y ≤ ENNReal.ofReal (((a : ℝ) - 1) * meshSize L i)) ∧
  (IsPartitionRegion i Y →
    layerEnlargement i (cubeHull i Y) ((a : ℤ) - 1) = layerEnlargement i Y (a : ℤ))
def PartitionGeometryStatement : Prop :=
  (∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i i' : ℤ, -(m : ℤ) ≤ i →
    i ≤ i' → CoarserPartitionRefines L m i i') ∧
  (∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ (i : ℤ) (n : ℕ),
    -(m : ℤ) ≤ i → ∀ x : Site L m (i + n), SiteInteriorToCoarseCube L m i n x) ∧
  (∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ k : ℕ, k < K →
    BlockAverageSeesOnlyDoubleBlock L m K k) ∧
  (∀ (c : ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ),
    CubesOfStep.LargeFieldParameters c K x → 0 < m → ∀ k : ℕ, k < K →
      CubesOfStep.PartitionsFit c m K x (k + 1) → TestPartitionSubordinate c m K x k) ∧
  (∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ Y : Set (FourTorus L m), Y.Nonempty → IsClosed Y → ∀ a : ℕ, 1 ≤ a →
      LayerNeighborhoodCharacterization L m i Y a)
end PeriodicLattice
end YangMills.Construction
