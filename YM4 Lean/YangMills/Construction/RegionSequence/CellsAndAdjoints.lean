import YangMills.Construction.RegionSequence.FineLatticeNorms
import YangMills.Construction.RegionSequence.PastLastLevel
import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.RegionSequence.CellStructure
open NestedRegions
def IsSelfAdjointOn {V : Type} (X : Set V) (p : V → V → ℝ) (T : V → V) : Prop :=
  (∀ u ∈ X, T u ∈ X) ∧ ∀ u ∈ X, ∀ v ∈ X, p (T u) v = p u (T v)
def IsFormNonneg {V : Type} (X : Set V) (p : V → V → ℝ) (T : V → V) : Prop :=
  ∀ u ∈ X, 0 ≤ p u (T u)
def IsFormPosDef {V : Type} [Zero V] (X : Set V) (p : V → V → ℝ) (T : V → V) : Prop :=
  ∀ u ∈ X, u ≠ 0 → 0 < p u (T u)
variable (𝒮 : NestedRegions)
def shellCubes (j : ℕ) : Set (Set 𝒮.Point) :=
  {Q ∈ 𝒮.cubePartitionAt j | Q ⊆ 𝒮.Ω j ∧ ¬ Q ⊆ 𝒮.Ω (j + 1)}
variable {𝒮}
def tensorFwdDiff {r : ℕ} (ν : Fin 4) (J : 𝒮.Tensor r) : 𝒮.Tensor r :=
  fun κ => fwdDiff ν (J κ)
def tensorBwdDiff {r : ℕ} (ν : Fin 4) (J : 𝒮.Tensor r) : 𝒮.Tensor r :=
  fun κ => bwdDiff ν (J κ)
variable (𝒮)
structure PartitionFacts : Prop where
  faces : ∀ i, 𝒮.IsPartitionLevel i → ∀ Q ∈ 𝒮.cubePartitionAt i, ∀ p ∈ frontier Q,
    ∃ (μ : Fin 4) (k : ℤ), p μ = ((((k : ℝ) + 1 / 2) * 𝒮.scale i : ℝ) : AddCircle 𝒮.side)
  cube_eq_union : ∀ i i', i ≤ i' → 𝒮.IsPartitionLevel i' → ∀ Q ∈ 𝒮.cubePartitionAt i',
    Q = ⋃₀ {Q' ∈ 𝒮.cubePartitionAt i | Q' ⊆ Q}
  site_interior : ∀ i i', i ≤ i' → 𝒮.IsPartitionLevel i' →
    ∀ x ∈ spacingLattice 4 𝒮.side (𝒮.scale i), ∃ Q ∈ 𝒮.cubePartitionAt i', x ∈ interior Q ∧
      ∀ Q' ∈ 𝒮.cubePartitionAt i', x ∈ Q' → Q' = Q
  complement_eq_closure : ∀ i', 𝒮.IsPartitionLevel i' → ∀ X, 𝒮.IsCubeUnionAt i' X →
    𝒮.cubeComplementAt i' X = closure Xᶜ
  complement_same : ∀ i i', i ≤ i' → 𝒮.IsPartitionLevel i' → ∀ X, 𝒮.IsCubeUnionAt i' X →
    𝒮.IsCubeUnionAt i X ∧ 𝒮.cubeComplementAt i X = 𝒮.cubeComplementAt i' X
  block_sites : ∀ n ≤ 𝒮.s, ∀ y ∈ spacingLattice 4 𝒮.side (𝒮.scale n),
    {x : 𝒮.FineSite | (x : 𝒮.Point) ∈ cubeAt y (𝒮.scale n)} = 𝒮.fineBlock n y ∧
      (𝒮.fineBlock n y).ncard = 𝒮.L ^ (n * 4)
structure CellFacts : Prop where
  regions : ∀ j ≤ 𝒮.s, 𝒮.IsCubeUnionAt j (𝒮.Ω j) ∧ 𝒮.IsCubeUnionAt j (𝒮.Ω (j + 1))
  shell_eq : ∀ j ≤ 𝒮.s, 𝒮.shellOf j = ⋃₀ shellCubes 𝒮 j
  shellCubes_eq : ∀ j ≤ 𝒮.s, shellCubes 𝒮 j = 𝒮.cellOf '' 𝒮.centresAt j
  interior_disjoint : ∀ j ≤ 𝒮.s, ∀ Q ∈ shellCubes 𝒮 j, Disjoint (interior Q) (𝒮.Ω (j + 1))
  cell_subset : ∀ j ≤ 𝒮.s, ∀ y ∈ 𝒮.centresAt j, 𝒮.cellOf y ⊆ 𝒮.shellOf j ∧
    𝒮.shellOf j ⊆ 𝒮.Ω j ∩ 𝒮.cubeComplementAt j (𝒮.Ω (j + 1))
  interiors_disjoint : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, y ≠ y' →
    Disjoint (interior (𝒮.cellOf y)) (interior (𝒮.cellOf y'))
  union_eq : ⋃ y ∈ 𝒮.allCentres, 𝒮.cellOf y = 𝒮.Ω 0
  fine_site : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.Ω 0 → ∃ y ∈ 𝒮.allCentres,
    (x : 𝒮.Point) ∈ interior (𝒮.cellOf y) ∧ ∀ y' ∈ 𝒮.allCentres, (x : 𝒮.Point) ∈ 𝒮.cellOf y' → y' = y
structure AnchorFacts : Prop where
  anchor_spec : ∀ b ∈ 𝒮.bonds, (𝒮.anchor b : 𝒮.Point) ∈ 𝒮.Ω 0 ∧
    supNorm ((𝒮.anchor b : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ ∧
    (𝒮.anchor b ≠ b.source → (b.source : 𝒮.Point) ∉ 𝒮.Ω 0 ∧ 𝒮.anchor b = b.target)
  sum_cutSite : ∀ f ∈ 𝒮.siteFns, ∑ᶠ y ∈ 𝒮.allCentres, cellCutSite y f = f
  sum_cutBond : ∀ A ∈ 𝒮.oneForms, ∑ᶠ y ∈ 𝒮.allCentres, cellCutBond y A = A
  sum_cutTensor : ∀ r : ℕ, r = 1 ∨ r = 2 → ∀ J : 𝒮.Tensor r,
    (∀ κ, AnchorSupported (𝒮.Ω 0) (J κ)) → ∑ᶠ y ∈ 𝒮.allCentres, cellCutTensor y J = J
  sum_pointCut : ∀ ω : 𝒮.Coarse, ∑ᶠ y : 𝒮.allCentres, pointCut y ω = ω
  cutSite_cutSite : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, y ≠ y' → ∀ f ∈ 𝒮.siteFns,
    cellCutSite y (cellCutSite y' f) = 0
  cutBond_cutBond : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, y ≠ y' → ∀ A ∈ 𝒮.oneForms,
    cellCutBond y (cellCutBond y' A) = 0
  cutTensor_cutTensor : ∀ r : ℕ, r = 1 ∨ r = 2 → ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, y ≠ y' →
    ∀ J : 𝒮.Tensor r, (∀ κ, AnchorSupported (𝒮.Ω 0) (J κ)) →
      cellCutTensor y (cellCutTensor y' J) = 0
  pointCut_pointCut : ∀ y y' : 𝒮.allCentres, y ≠ y' → ∀ ω : 𝒮.Coarse,
    pointCut y (pointCut y' ω) = 0
  bonds_in_cell_le : ∀ y ∈ 𝒮.allCentres,
    (({b ∈ 𝒮.bonds | AnchoredIn (𝒮.cellOf y) b}.ncard : ℕ) : ℝ) ≤
      2 * 4 * (𝒮.levelScale y / 𝒮.ξ) ^ 4
  bonds_in_cell_eq : 𝒮.Ω 0 = univ → ∀ y ∈ 𝒮.allCentres,
    (({b ∈ 𝒮.bonds | AnchoredIn (𝒮.cellOf y) b}.ncard : ℕ) : ℝ) = 4 * (𝒮.levelScale y / 𝒮.ξ) ^ 4
  doubled_cell : ∀ K m M R₁ : ℕ, 0 < K → 0 < m → 𝒮.s ≤ K → 𝒮.ξ = unitSpacing 𝒮.L 𝒮.s →
    𝒮.side = unitSide 𝒮.L m K 𝒮.s → IsSeparatedChain 𝒮.L 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω →
    ∀ y ∈ 𝒮.allCentres, doubledSiteCube 𝒮.L 𝒮.ξ 𝒮.Ω y = cubeHalfSide y (𝒮.levelScale y) ∧
      𝒮.cellOf y ⊆ cubeHalfSide y (𝒮.levelScale y)
structure AdjointFacts : Prop where
  site_adjoint : ∀ (ν : Fin 4) (f g : 𝒮.FineSite → ℝ),
    innerSum (forwardDiff ν f) g = innerSum f (backwardDiff ν g)
  site_star : ∀ (ν : Fin 4) (f : 𝒮.FineSite → ℝ),
    backwardDiff ν f = 𝒮.ξ⁻¹ • (translateBackward ν f - f) ∧
      backwardDiff ν f = -translateBackward ν (forwardDiff ν f)
  site_commute : ∀ (ν ρ : Fin 4) (f : 𝒮.FineSite → ℝ),
    forwardDiff ν (forwardDiff ρ f) = forwardDiff ρ (forwardDiff ν f) ∧
      forwardDiff ν (backwardDiff ρ f) = backwardDiff ρ (forwardDiff ν f) ∧
      backwardDiff ν (backwardDiff ρ f) = backwardDiff ρ (backwardDiff ν f)
  bond_adjoint : ∀ (ν : Fin 4) (A B : 𝒮.FineBond → ℝ),
    bondInner (fwdDiff ν A) B = bondInner A (bwdDiff ν B)
  bond_star : ∀ (ν : Fin 4) (A : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond),
    bwdDiff ν A b = 𝒮.ξ⁻¹ * (A (shiftDown ν b) - A b) ∧
      bwdDiff ν A b = -fwdDiff ν A (shiftDown ν b)
  bond_commute : ∀ (ν ρ : Fin 4) (A : 𝒮.FineBond → ℝ),
    fwdDiff ν (fwdDiff ρ A) = fwdDiff ρ (fwdDiff ν A) ∧
      fwdDiff ν (bwdDiff ρ A) = bwdDiff ρ (fwdDiff ν A) ∧
      bwdDiff ν (bwdDiff ρ A) = bwdDiff ρ (bwdDiff ν A)
  tensor_adjoint : ∀ r : ℕ, r = 1 ∨ r = 2 → ∀ (ν : Fin 4) (J J' : 𝒮.Tensor r),
    tensorInner (tensorFwdDiff ν J) J' = tensorInner J (tensorBwdDiff ν J')
  tensor_star : ∀ r : ℕ, r = 1 ∨ r = 2 → ∀ (ν : Fin 4) (J : 𝒮.Tensor r)
    (κ : Fin r → Fin 4) (b : 𝒮.FineBond),
    tensorBwdDiff ν J κ b = 𝒮.ξ⁻¹ * (J κ (shiftDown ν b) - J κ b) ∧
      tensorBwdDiff ν J κ b = -tensorFwdDiff ν J κ (shiftDown ν b)
  tensor_commute : ∀ r : ℕ, r = 1 ∨ r = 2 → ∀ (ν ρ : Fin 4) (J : 𝒮.Tensor r),
    tensorFwdDiff ν (tensorFwdDiff ρ J) = tensorFwdDiff ρ (tensorFwdDiff ν J) ∧
      tensorFwdDiff ν (tensorBwdDiff ρ J) = tensorBwdDiff ρ (tensorFwdDiff ν J) ∧
      tensorBwdDiff ν (tensorBwdDiff ρ J) = tensorBwdDiff ρ (tensorBwdDiff ν J)
  nabla_adjoint : ∀ J : 𝒮.Tensor 1, divOne J ∈ 𝒮.oneForms ∧
    ∀ A ∈ 𝒮.oneForms, tensorInner (nablaOne A) J = bondInner A (divOne J)
  divOne_apply : ∀ (J : 𝒮.Tensor 1), ∀ b ∈ 𝒮.bonds,
    divOne J b = ∑ ν, bwdDiff ν (J (constIdx ν)) b
  dDir_adjoint : ∀ A ∈ 𝒮.oneForms, dDirAdj A ∈ 𝒮.siteFns ∧
    ∀ f ∈ 𝒮.siteFns, bondInner (dDir f) A = innerSum f (dDirAdj A)
  avgAdj_apply : ∀ ω : 𝒮.Coarse, blockAvgAdj ω ∈ 𝒮.siteFns ∧
    ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.Ω 0 → ∃ h : 𝒮.centreOfSite x ∈ 𝒮.allCentres,
      blockAvgAdj ω x = ω ⟨𝒮.centreOfSite x, h⟩
  avg_avgAdj : ∀ ω : 𝒮.Coarse, blockAvg (blockAvgAdj ω) = ω
  avgAdj_injective : Function.Injective (blockAvgAdj (𝒮 := 𝒮))
  weighted_apply : ∀ f ∈ 𝒮.siteFns, ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.Ω 0 →
    ∃ h : 𝒮.centreOfSite x ∈ 𝒮.allCentres,
      blockAvgAdj (weightMul (blockAvg f)) x =
        blockWeights 𝒮.L (𝒮.level (𝒮.centreOfSite x)) *
          (𝒮.scale (𝒮.level (𝒮.centreOfSite x)) ^ 2)⁻¹ * blockAvg f ⟨𝒮.centreOfSite x, h⟩
  avg_le_sup : ∀ f ∈ 𝒮.siteFns, ∀ y : 𝒮.allCentres,
    |blockAvg f y| ≤ supNormOn (𝒮.cellOf y) f
structure HodgeFacts : Prop where
  identity : ∀ A : 𝒮.FineBond → ℝ,
    curlTorusAdj (curlTorus A) + dTorus (dTorusAdj A) = bondLap A
  on_components : ∀ (A : 𝒮.FineBond → ℝ) (μ : Fin 4),
    comp (bondLap A) μ = latticeLaplacian (comp A μ)
  bounds : ∀ A : 𝒮.FineBond → ℝ, 0 ≤ bondInner A (curlTorusAdj (curlTorus A)) ∧
    bondInner A (curlTorusAdj (curlTorus A)) ≤ bondInner A (bondLap A) ∧
    bondInner A (bondLap A) ≤ 4 * 4 * (𝒮.ξ ^ 2)⁻¹ * bondInner A A
structure WeightFacts : Prop where
  nonneg : ∀ n, ∀ c ∈ 𝒮.coarseBonds n, ∀ b, 0 ≤ avgWeight n c b
  sum_eq_one : ∀ n, ∀ c ∈ 𝒮.coarseBonds n, ∑ᶠ b, avgWeight n c b = 1
  le : ∀ n, ∀ c ∈ 𝒮.coarseBonds n, ∀ b, avgWeight n c b ≤ ((𝒮.L : ℝ) ^ (n * 4))⁻¹
  support : ∀ n, ∀ c ∈ 𝒮.coarseBonds n, ∀ b, avgWeight n c b ≠ 0 →
    b.dir = c.dir ∧
      (b.source ∈ 𝒮.fineBlock n (c.source : 𝒮.Point) ∨
        b.source ∈ 𝒮.fineBlock n (c.target : 𝒮.Point))
structure PositivityFacts : Prop where
  gauge_symmetric : IsSelfAdjointOn (𝒮.siteFns : Set (𝒮.FineSite → ℝ)) innerSum gaugeLap
  gauge_positive :
    IsFormPosDef (𝒮.siteFns : Set (𝒮.FineSite → ℝ)) innerSum gaugeLap
  green_exists : ∀ f ∈ 𝒮.siteFns, gaugeGreenOp f ∈ 𝒮.siteFns ∧
    gaugeLap (gaugeGreenOp f) = f ∧ gaugeGreenOp (gaugeLap f) = f
  green_symmetric : IsSelfAdjointOn (𝒮.siteFns : Set (𝒮.FineSite → ℝ)) innerSum gaugeGreenOp
  averaged_symmetric :
    IsSelfAdjointOn (𝒮.oneForms : Set (𝒮.FineBond → ℝ)) bondInner avgOp
  averaged_nonneg :
    IsFormNonneg (𝒮.oneForms : Set (𝒮.FineBond → ℝ)) bondInner avgOp
  basic_symmetric :
    IsSelfAdjointOn (𝒮.oneForms : Set (𝒮.FineBond → ℝ)) bondInner baseOp
  basic_nonneg :
    IsFormNonneg (𝒮.oneForms : Set (𝒮.FineBond → ℝ)) bondInner baseOp
def CellStructureClaim : Prop :=
  ∀ 𝒮 : NestedRegions, PartitionFacts 𝒮 ∧ CellFacts 𝒮 ∧ AnchorFacts 𝒮 ∧ AdjointFacts 𝒮 ∧
    HodgeFacts 𝒮 ∧ WeightFacts 𝒮 ∧
    (∀ n, 1 - ((𝒮.L : ℝ) ^ 2)⁻¹ ≤ blockWeights 𝒮.L n ∧ blockWeights 𝒮.L n ≤ 1) ∧
    PositivityFacts 𝒮 ∧
    ∀ p q q' : 𝒮.Point,
      𝒮.weightedDist p q' ≤ 𝒮.weightedDist p q + 𝒮.weightedDist q q'
end YangMills.Construction.RegionSequence.CellStructure
