import YangMills.Construction.TorusForms.BlocksCorridorsAveragesTrees
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace Lattice
section Paths
variable {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ}
def stepsEndpoint : LatticeSite ℓ ε → List (LinkStep ℓ ε) → LatticeSite ℓ ε
  | x, [] => x
  | _, t :: ts => stepsEndpoint t.target ts
def LatticePath.endpoint (γ : LatticePath ℓ ε) : LatticeSite ℓ ε :=
  stepsEndpoint γ.origin γ.steps
end Paths
end Lattice
open YangMills.Construction.Lattice
namespace BlockSpin
variable (P : LatticeParameters) {ℓ : Fin P.d → ℝ} {ε ε' : ℝ} {n : ℕ}
def UniqueBlockDecomposition (h : IsBlockSpacing P n ℓ ε ε') : Prop :=
  ∀ x : LatticeSite ℓ ε, ∃! p : LatticeSite ℓ ε' × (Fin P.d → ℤ),
    InBlockIndexRange P n p.2 ∧ x = h.toFineSite p.1 + gridPoint ℓ ε p.2
def BlocksPartitionLattice (n : ℕ) (ℓ : Fin P.d → ℝ) (ε ε' : ℝ) : Prop :=
  (∀ x : LatticeSite ℓ ε, ∃! y : LatticeSite ℓ ε', x ∈ blockOf P n ε y) ∧
    ∀ y : LatticeSite ℓ ε', (blockOf P n ε y).ncard = P.L ^ (n * P.d)
def BlockTranslate (h : IsBlockSpacing P n ℓ ε ε') : Prop :=
  ∀ (y : LatticeSite ℓ ε') (μ : Fin P.d),
    (fun x : LatticeSite ℓ ε => x + h.toFineSite (latticeStep ℓ ε' μ)) '' blockOf P n ε y =
        blockOf P n ε (y + latticeStep ℓ ε' μ) ∧
      blockOf P n ε (y + latticeStep ℓ ε' μ) ≠ blockOf P n ε y
def BlockNeighborSite (h : IsBlockSpacing P n ℓ ε ε') : Prop :=
  ∀ (y : LatticeSite ℓ ε') (σ : Fin P.d → ℤ), InBlockIndexRange P n σ → ∀ μ : Fin P.d,
    (σ μ < (P.L : ℤ) ^ n - 1 - blockOffset P n →
      h.toFineSite y + gridPoint ℓ ε σ + latticeStep ℓ ε μ ∈ blockOf P n ε y) ∧
    (σ μ = (P.L : ℤ) ^ n - 1 - blockOffset P n →
      h.toFineSite y + gridPoint ℓ ε σ + latticeStep ℓ ε μ =
          h.toFineSite (y + latticeStep ℓ ε' μ) +
            gridPoint ℓ ε (σ - Pi.single μ ((P.L : ℤ) ^ n - 1)) ∧
        h.toFineSite y + gridPoint ℓ ε σ + latticeStep ℓ ε μ ∈
          blockOf P n ε (y + latticeStep ℓ ε' μ))
def NestedBlocks (n : ℕ) (ℓ : Fin P.d → ℝ) (ε ε' : ℝ) : Prop :=
  ∀ (m : ℕ) (ε'' : ℝ), IsBlockSpacing P (n + m) ℓ ε ε'' → ∀ z : LatticeSite ℓ ε'',
    blockOf P (n + m) ε z = blockUnion P n ε (blockOf P m ε' z) ∧
      (blockOf P m ε' z).PairwiseDisjoint (blockOf P n ε)
def LinkInBlockOrCorridor (n : ℕ) (ℓ : Fin P.d → ℝ) (ε ε' : ℝ) : Prop :=
  (∀ b : Link ℓ ε,
    ((∃! y : LatticeSite ℓ ε', LinkInside P b (blockOf P n ε y)) ∧
        ∀ c : Link ℓ ε', b ∉ linkCorridor P n ε c) ∨
      ((∃! c : Link ℓ ε', b ∈ linkCorridor P n ε c) ∧
        ∀ y : LatticeSite ℓ ε', ¬ LinkInside P b (blockOf P n ε y))) ∧
  ∀ c : Link ℓ ε', ∀ b ∈ linkCorridor P n ε c,
    (b.1 ∈ blockOf P n ε c.1 ∧ b.head ∈ blockOf P n ε c.head) ∨
      (b.1 ∈ blockOf P n ε c.head ∧ b.head ∈ blockOf P n ε c.1)
def PlaquettesOfCorridors (n : ℕ) (ℓ : Fin P.d → ℝ) (ε ε' : ℝ) : Prop :=
  (∀ (c : Link ℓ ε') (q : LatticePlaquette ℓ ε),
    PlaquetteInLinkCorridor P n q c ↔
      ∃ (ν : Fin P.d) (x : LatticeSite ℓ ε), ν ≠ c.2 ∧
        q.vertices = {x, x + latticeStep ℓ ε c.2, x + latticeStep ℓ ε c.2 + latticeStep ℓ ε ν,
          x + latticeStep ℓ ε ν} ∧
        (x, c.2) ∈ linkCorridor P n ε c ∧ (x + latticeStep ℓ ε ν, c.2) ∈ linkCorridor P n ε c) ∧
  (∀ (c : Link ℓ ε') (ν : Fin P.d) (x : LatticeSite ℓ ε), ν ≠ c.2 →
    (x, c.2) ∈ linkCorridor P n ε c → (x + latticeStep ℓ ε ν, c.2) ∈ linkCorridor P n ε c →
      LinkInside P (x, ν) (blockOf P n ε c.1) ∧
        LinkInside P (x + latticeStep ℓ ε c.2, ν) (blockOf P n ε c.head)) ∧
  (∀ (c c' : Link ℓ ε') (q : LatticePlaquette ℓ ε),
    PlaquetteInLinkCorridor P n q c → PlaquetteInLinkCorridor P n q c' → c' = c) ∧
  (∀ (c : Link ℓ ε') (q : LatticePlaquette ℓ ε), PlaquetteInLinkCorridor P n q c →
    ∀ y : LatticeSite ℓ ε', ¬ PlaquetteWithin P q (blockOf P n ε y)) ∧
  ∀ (q : LatticePlaquette ℓ ε) (y y' : LatticeSite ℓ ε'),
    PlaquetteWithin P q (blockOf P n ε y) → PlaquetteWithin P q (blockOf P n ε y') → y' = y
def LinkDomainEndpoints (n : ℕ) (ℓ : Fin P.d → ℝ) (ε ε' : ℝ) : Prop :=
  ∀ b : Link ℓ ε', ∀ a ∈ linkDomain P n ε b,
    a.ends ⊆ blockOf P n ε b.1 ∪ blockOf P n ε b.head
def BlockPathConnected (n : ℕ) (ℓ : Fin P.d → ℝ) (ε ε' : ℝ) : Prop :=
  ∀ (y : LatticeSite ℓ ε'), ∀ x ∈ blockOf P n ε y, ∀ x' ∈ blockOf P n ε y,
    ∃ γ : LatticePath ℓ ε, γ.origin = x ∧ γ.endpoint = x' ∧
      ∀ t ∈ γ.steps, LinkInside P t.link (blockOf P n ε y)
def TrivialBlocks (ℓ : Fin P.d → ℝ) (ε : ℝ) [IsCommensurateSpacing ℓ ε] : Prop :=
  (∀ y : LatticeSite ℓ ε, blockOf P 0 ε y = {y}) ∧
    blockAverage0 P (ℓ := ℓ) 0 ε ε = LinearMap.id ∧
    blockAverage1 P (ℓ := ℓ) 0 ε ε = LinearMap.id
def BlockTreeCoordinateFormula (h : IsBlockSpacing P 1 ℓ ε ε') : Prop :=
  ∀ y : LatticeSite ℓ ε',
    blockTree P h y = blockTreeByCoordinates P ε y ∧
    (∀ b ∈ blockTree P h y, LinkInside P b (blockOf P 1 ε y)) ∧
    ∀ B : Cochain1 ℓ ε, (∀ b ∈ blockTree P h y, B b = 0) ↔
      ∀ (x : LatticeSite ℓ ε) (hx : x ∈ blockOf P 1 ε y), pathIntegral B (blockContour P h y hx) = 0
def BlockAverage0AdjointConstant (n : ℕ) (ℓ : Fin P.d → ℝ) (ε ε' : ℝ) [IsCommensurateSpacing ℓ ε]
    [IsCommensurateSpacing ℓ ε'] : Prop :=
  ∀ (ω : Cochain0 ℓ ε') (y : LatticeSite ℓ ε'), ∀ x ∈ blockOf P n ε y,
    blockAverage0Adjoint P n ε ε' ω x = ω y
def DivergenceLaplacianFormulas (ℓ : Fin P.d → ℝ) (ε : ℝ) [IsCommensurateSpacing ℓ ε] : Prop :=
  (∀ (A : Cochain1 ℓ ε) (x : LatticeSite ℓ ε),
    latticeDivergence ℓ ε A x =
      ε⁻¹ * ∑ μ, (linkComponent A μ (x - latticeStep ℓ ε μ) - linkComponent A μ x)) ∧
  ∀ (f : Cochain0 ℓ ε) (x : LatticeSite ℓ ε),
    latticeLaplacian0 ℓ ε f x =
      (ε ^ 2)⁻¹ * ∑ μ, ((f x - f (x + latticeStep ℓ ε μ)) + (f x - f (x - latticeStep ℓ ε μ)))
def BlockGeometry : Prop :=
  (∀ (P : LatticeParameters) (ℓ : Fin P.d → ℝ) (ε ε' : ℝ) (n : ℕ) [IsCommensurateSpacing ℓ ε]
      [IsCommensurateSpacing ℓ ε'] (h : IsBlockSpacing P n ℓ ε ε'),
    UniqueBlockDecomposition P h ∧ BlocksPartitionLattice P n ℓ ε ε' ∧ BlockTranslate P h ∧
      BlockNeighborSite P h ∧ NestedBlocks P n ℓ ε ε' ∧
      LinkInBlockOrCorridor P n ℓ ε ε' ∧ PlaquettesOfCorridors P n ℓ ε ε' ∧
      LinkDomainEndpoints P n ℓ ε ε' ∧ BlockPathConnected P n ℓ ε ε' ∧
      BlockAverage0AdjointConstant P n ℓ ε ε' ∧ DivergenceLaplacianFormulas P ℓ ε) ∧
  (∀ (P : LatticeParameters) (ℓ : Fin P.d → ℝ) (ε : ℝ) [IsCommensurateSpacing ℓ ε],
    IsBlockSpacing P 0 ℓ ε ε → TrivialBlocks P ℓ ε) ∧
  ∀ (P : LatticeParameters) (ℓ : Fin P.d → ℝ) (ε ε' : ℝ) [IsCommensurateSpacing ℓ ε]
    (h : IsBlockSpacing P 1 ℓ ε ε'), BlockTreeCoordinateFormula P h
end BlockSpin
end YangMills.Construction
