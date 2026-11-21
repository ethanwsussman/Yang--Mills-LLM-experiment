import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace PeriodicLattice
def blockAsGrid {L m : ℕ} {i : ℤ} (n : ℕ) (y : Site L m i) : Set (FourTorus L m) :=
  {x | ∃ p : Fin 4 → ℤ, (∀ μ, |(p μ : ℝ)| ≤ ((L : ℝ) ^ n - 1) / 2) ∧
    x = (y : FourTorus L m) + torusProj (torusSide L m) fun μ => meshSize L (i + n) * (p μ : ℝ)}
def HyperplaneContainsFace (L m : ℕ) (i : ℤ) (μ : Fin 4) (c : AddCircle (torusSide L m)) : Prop :=
  ∃ F Q : Set (FourTorus L m), IsCubeFace i F Q ∧ F ⊆ {x | x μ = c}
def RefinementCubeFacts (L m : ℕ) (i : ℤ) (n : ℕ) : Prop :=
  (∀ y : Site L m i, refinedBlock n y = blockAsGrid n y) ∧
  (∀ y : Site L m i, cubeAround y =
    ⋃ y' : Site L m (i + n), ⋃ _ : (y' : FourTorus L m) ∈ refinedBlock n y, cubeAround y') ∧
  (∀ Q ∈ standardCubePartition L m (i + n), ∃ Q' ∈ standardCubePartition L m i, Q ⊆ Q') ∧
  (∀ X : Set (FourTorus L m), IsPartitionRegion i X → IsPartitionRegion (i + n) X) ∧
  (∀ (μ : Fin 4) (c : AddCircle (torusSide L m)),
    HyperplaneContainsFace L m i μ c → HyperplaneContainsFace L m (i + n) μ c)
def CubeSupDistanceFacts (L m : ℕ) (i : ℤ) : Prop :=
  (∀ y y' : Site L m i, ∃ n : ℕ,
    torusSupNorm ((y : FourTorus L m) - (y' : FourTorus L m)) = (n : ℝ) * meshSize L i) ∧
  (∀ y y' : Site L m i, setSupDist (cubeAround y) (cubeAround y') =
    ENNReal.ofReal (max 0 (torusSupNorm ((y : FourTorus L m) - (y' : FourTorus L m)) - meshSize L i))) ∧
  (∀ y y' : Site L m i, CubesMeet (cubeAround y) (cubeAround y') ↔
    torusSupNorm ((y : FourTorus L m) - (y' : FourTorus L m)) ≤ meshSize L i) ∧
  (∀ Q ∈ standardCubePartition L m i, ∀ Q' ∈ standardCubePartition L m i, ¬CubesMeet Q Q' →
    ENNReal.ofReal (meshSize L i) ≤ setSupDist Q Q') ∧
  ⋃₀ standardCubePartition L m i = univ ∧
  (∀ (y : Site L m i) (x : FourTorus L m), torusSupNorm (x - (y : FourTorus L m)) < meshSize L i / 2 →
    ∀ Q ∈ standardCubePartition L m i, x ∈ Q → Q = cubeAround y) ∧
  (∀ C ⊆ standardCubePartition L m i, ∀ Q ∈ standardCubePartition L m i, Q ⊆ ⋃₀ C → Q ∈ C)
def EnlargementViaCentres (L m : ℕ) (i : ℤ) : Prop :=
  (∀ X : Set (FourTorus L m), IsPartitionRegion i X → ∀ (a : ℕ) (y' : Site L m i),
    cubeAround y' ∈ partitionCubesIn i (layerEnlargement i X (a : ℤ)) ↔
      ∃ y : Site L m i, cubeAround y ∈ partitionCubesIn i X ∧
        torusSupNorm ((y' : FourTorus L m) - (y : FourTorus L m)) ≤ (a : ℝ) * meshSize L i) ∧
  (∀ X : Set (FourTorus L m), IsPartitionRegion i X → ∀ a : ℕ, X ⊆ layerEnlargement i X (a : ℤ)) ∧
  (∀ X₁ X₂ : Set (FourTorus L m), IsPartitionRegion i X₁ → IsPartitionRegion i X₂ → ∀ a : ℕ,
    X₁ ⊆ X₂ → layerEnlargement i X₁ (a : ℤ) ⊆ layerEnlargement i X₂ (a : ℤ)) ∧
  (∀ X₁ X₂ : Set (FourTorus L m), IsPartitionRegion i X₁ → IsPartitionRegion i X₂ → ∀ a : ℕ,
    layerEnlargement i (X₁ ∪ X₂) (a : ℤ) =
      layerEnlargement i X₁ (a : ℤ) ∪ layerEnlargement i X₂ (a : ℤ)) ∧
  (∀ X : Set (FourTorus L m), IsPartitionRegion i X → ∀ a b : ℕ,
    layerEnlargement i (layerEnlargement i X (a : ℤ)) (b : ℤ) =
      layerEnlargement i X ((a + b : ℕ) : ℤ))
def EnlargementSupDistanceFacts (L m : ℕ) (i : ℤ) : Prop :=
  ∀ X : Set (FourTorus L m), IsPartitionRegion i X → ∀ a : ℕ,
    (∀ x ∈ layerEnlargement i X (a : ℤ),
      setSupDist {x} X ≤ ENNReal.ofReal ((a : ℝ) * meshSize L i)) ∧
    (∀ Q ∈ standardCubePartition L m i, Q ∉ partitionCubesIn i (layerEnlargement i X (a : ℤ)) →
      ENNReal.ofReal ((a : ℝ) * meshSize L i) ≤ setSupDist Q X) ∧
    (1 ≤ a → ∀ Q ∈ partitionCubesIn i (layerEnlargement i X (a : ℤ)),
      setSupDist Q X ≤ ENNReal.ofReal (((a : ℝ) - 1) * meshSize L i)) ∧
    (∀ x : FourTorus L m, setSupDist {x} X < ENNReal.ofReal ((a : ℝ) * meshSize L i) →
      x ∈ layerEnlargement i X (a : ℤ) ∧
        ∀ Q ∈ partitionCubesIn i (complementRegion i (layerEnlargement i X (a : ℤ))), x ∉ Q)
def ComponentBoxesAreRegions (L m : ℕ) (i : ℤ) : Prop :=
  ∀ X : Set (FourTorus L m), IsPartitionRegion i X →
    (∀ C, IsSmallRegionComponent i X C → IsPartitionRegion i (componentBox i C)) ∧
    IsPartitionRegion i (boxingOnce i X) ∧ X ⊆ boxingOnce i X ∧
    IsPartitionRegion i (boxClosure i X) ∧ X ⊆ boxClosure i X
def StandardPartitionCubeGeometry : Prop :=
  ∀ L m : ℕ, Odd L → 13 ≤ L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    (∀ n : ℕ, RefinementCubeFacts L m i n) ∧
    CubeSupDistanceFacts L m i ∧
    EnlargementViaCentres L m i ∧
    EnlargementSupDistanceFacts L m i ∧
    ComponentBoxesAreRegions L m i
end PeriodicLattice
end YangMills.Construction
end
