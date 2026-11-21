import YangMills.Construction.Torus.CoversAndLocalisationData
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
def faceCoords (σ : ℝ) : Set ℝ := {a | ∃ k : ℤ, a = σ * ((k : ℝ) + 1 / 2)}
namespace TorusData
variable (D : TorusData)
def InUniqueCubeInterior (σ : ℝ) (x : D.Space) : Prop :=
  ∃ β ∈ D.partitionAt σ, x ∈ interior β ∧
    ∀ β' ∈ D.partitionAt σ, x ∈ β' → β' = β
def PartitionFacts (σ : ℝ) : Prop :=
  (∃ N : ℤ, Even N ∧ D.side = N * σ) ∧
  (∀ v : Fin 4 → ℝ, (∀ μ, v μ ∉ faceCoords σ) →
    (∀ w : Fin 4 → ℝ, TorusMetric.torusProj D.side w = TorusMetric.torusProj D.side v →
        ∀ μ, w μ ∉ faceCoords σ) ∧
      D.InUniqueCubeInterior σ (TorusMetric.torusProj D.side v)) ∧
  ∀ β ∈ D.partitionAt σ, closure (interior β) = β ∧
    ∀ β' ∈ D.partitionAt σ, β' ≠ β → Disjoint (interior β) β'
def RefinementFacts (σ σ' : ℝ) : Prop :=
  faceCoords σ' ⊆ faceCoords σ ∧
  (∀ x ∈ D.latticeAt σ, D.InUniqueCubeInterior σ' x) ∧
  (∀ β ∈ D.partitionAt σ, ∃! β', β' ∈ D.partitionAt σ' ∧ β ⊆ β') ∧
  (∀ β' ∈ D.partitionAt σ', β' = ⋃₀ {β ∈ D.partitionAt σ | β ⊆ β'}) ∧
  ∀ X : Set D.Space, D.IsCubeUnionAt σ' X →
    D.IsCubeUnionAt σ X ∧ D.IsCubeUnionAt σ (D.closedComplement X) ∧
      ∀ β ∈ D.partitionAt σ,
        (β ⊆ X ∧ ¬ β ⊆ D.closedComplement X ∧ Disjoint (interior β) (D.closedComplement X)) ∨
        (β ⊆ D.closedComplement X ∧ ¬ β ⊆ X ∧ Disjoint (interior β) X)
def BlockCubeFacts (m n : ℕ) : Prop :=
  D.partitionAt (D.blockSide n) = D.partitionAt (D.scale (n + m)) ∧
  (∃ N : ℤ, Even N ∧ D.side / D.blockSide n = N) ∧
  2 * D.blockSide n ≤ D.side ∧
  2 * (D.L : ℝ) * D.scale n ≤ 2 * D.blockSide n
def blockCubesAt (j : ℕ) (z : D.Space) : Set (Set D.Space) :=
  {β | ∃ y ∈ D.latticeAt (D.blockSide j),
    z ∈ D.cubeVertices (D.blockSide j) y ∧ β = D.cubeAround (D.blockSide j) y}
def CornerBallFacts (j : ℕ) (z : D.Space) : Prop :=
  (∀ r : ℕ, 1 ≤ r → D.IsCubeUnionAt (D.blockSide j)
    {x | TorusMetric.torusSupNorm (x - z) ≤ (r : ℝ) * D.blockSide j}) ∧
  {x | TorusMetric.torusSupNorm (x - z) ≤ D.blockSide j} = ⋃₀ D.blockCubesAt j z ∧
  (D.blockCubesAt j z).ncard = 2 ^ 4
def blockOffsets (n : ℕ) : Set (Fin 4 → ℤ) :=
  {σ | ∀ μ, |(σ μ : ℝ)| ≤ ((D.L : ℝ) ^ n - 1) / 2}
def shiftedSite (y : D.Space) (σ : Fin 4 → ℤ) : D.Space :=
  y + TorusMetric.torusProj D.side fun μ => D.scale 0 * (σ μ : ℝ)
end TorusData
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def LayerDecomposition (n : ℕ) : Prop :=
  B.layer n = ⋃₀ {β ∈ D.partitionAt (D.blockSide n) |
    β ⊆ B.stage n ∧ ¬ β ⊆ B.stage (n + 1)} ∧
  B.stage n \ B.stage (n + 1) ⊆ B.layer n ∧
  B.layer n ⊆ B.stage n ∩ D.closedComplement (B.stage (n + 1)) ∧
  B.layer n = ⋃ y ∈ B.layerSites n, B.siteCube y
def SiteCubesTile : Prop :=
  (∀ y ∈ B.allSites, ∀ y' ∈ B.allSites, y ≠ y' →
    Disjoint (interior (B.siteCube y)) (interior (B.siteCube y'))) ∧
  (⋃ y ∈ B.allSites, B.siteCube y) = B.stage 0 ∧
  ∀ x : D.BareSite, (x : D.Space) ∈ B.stage 0 →
    ∃ y ∈ B.allSites, (x : D.Space) ∈ interior (B.siteCube y) ∧
      ∀ y' ∈ B.allSites, (x : D.Space) ∈ B.siteCube y' → y' = y
def BlocksPartition : Prop :=
  (∀ y ∈ B.allSites, ∀ y' ∈ B.allSites, y ≠ y' → Disjoint (B.block y) (B.block y')) ∧
  ⋃ y ∈ B.allSites, B.block y = D.bareSites (B.stage 0)
def BlockDescription (n : ℕ) (y : D.Space) : Prop :=
  Subtype.val '' B.block y = D.shiftedSite y '' D.blockOffsets n ∧
  InjOn (D.shiftedSite y) (D.blockOffsets n) ∧
  (B.block y).ncard = D.L ^ (n * 4) ∧
  (D.L : ℝ) ^ (n * 4) = (B.siteScale y / D.scale 0) ^ 4 ∧
  y ∈ Subtype.val '' B.block y ∧
  B.bareSpaceNorm (B.blockIndicator y) = B.siteScale y ^ 2
end SeparatedChain
def CubesLayersBlocksBallsHold : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D) (m : ℕ), D.blockNumber = D.L ^ m →
    ∀ i i' : ℕ, i ≤ i' → D.scale i' ≤ (D.blockNumber : ℝ) * D.scale D.top →
      D.PartitionFacts (D.scale i) ∧
      D.RefinementFacts (D.scale i) (D.scale i') ∧
      (∀ n, n ≤ D.top → D.BlockCubeFacts m n) ∧
      (∀ n, n ≤ D.top → B.LayerDecomposition n) ∧
      B.SiteCubesTile ∧
      B.BlocksPartition ∧
      (∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y) ∧
      (∀ x : D.BareSite, (x : D.Space) ∈ B.stage 0 → (x : D.Space) ∈ B.stage (B.bareLevel x)) ∧
      ∀ j, j ≤ D.top → ∀ z ∈ D.levelVertices j, D.CornerBallFacts j z
end YangMills.Construction.Weighted
