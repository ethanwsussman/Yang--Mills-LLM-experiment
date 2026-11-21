import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubeTorusTransfer
import YangMills.Construction.RegionSequence.FineLatticeNorms
import YangMills.Construction.RegionSequence.PastLastLevel
import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.CubeGeometry
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
def liftToSpace (φ : 𝒮.Point → ℝ) (p : Fin 4 → ℝ) : ℝ := φ (torusProj 4 𝒮.side p)
def restrictToFine (φ : 𝒮.Point → ℝ) (x : 𝒮.FineSite) : ℝ := φ (x : 𝒮.Point)
def IsFirstOrderDiff (D : (𝒮.FineSite → ℝ) → 𝒮.FineSite → ℝ) : Prop :=
  ∃ ν : Fin 4, D = forwardDiff ν ∨ D = backwardDiff ν
structure IsScaleBounded (c r : ℝ) (φ : 𝒮.Point → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  le_one : ∀ x, φ x ≤ 1
  smooth : ContDiff ℝ 2 (liftToSpace φ)
  derivative : ∀ i ≤ 2, ∀ (μ : Fin i → Fin 4) (p : Fin 4 → ℝ),
    |iteratedFDeriv ℝ i (liftToSpace φ) p fun k => Pi.single (μ k) 1| ≤ c * r⁻¹ ^ i
  difference : ∀ D : (𝒮.FineSite → ℝ) → 𝒮.FineSite → ℝ, IsFirstOrderDiff D →
    ∀ x, |D (restrictToFine φ) x| ≤ c * r⁻¹
  second_difference : ∀ D D' : (𝒮.FineSite → ℝ) → 𝒮.FineSite → ℝ, IsFirstOrderDiff D →
    IsFirstOrderDiff D' → ∀ x, |D (D' (restrictToFine φ)) x| ≤ c * r⁻¹ ^ 2
  lipschitz : ∀ x x', |φ x - φ x'| ≤ c * r⁻¹ * lOneNorm (x - x')
def HasCornerCellInShell (Q : LevelCube 𝒮 M) : Prop :=
  ∃ c ∈ spacingLattice 4 𝒮.side (cubeSide 𝒮 M Q.level),
    IsCornerOf 𝒮 c (cubeSide 𝒮 M Q.level) Q.centre ∧
    cubeAt c (cubeSide 𝒮 M Q.level) ⊆ 𝒮.shellOf Q.level
def activeNear (𝒮 : RegionSequence.NestedRegions) (M : ℕ) (y : 𝒮.Point) : Set (LevelCube 𝒮 M) :=
  {Q | Q ∈ active 𝒮 M ∧ (Q.supp ∩ cubeHalfSide y (4 * 𝒮.levelScale y)).Nonempty}
def CellMeetsThicken (Q : LevelCube 𝒮 M) (y : 𝒮.Point) : Prop :=
  (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty
def TorusCellMeetsThicken (Q : LevelCube 𝒮 M) (y' : Q.system.setting.Point) : Prop :=
  (Q.system.setting.cellOf y' ∩ Q.system.embed '' Q.thicken (5 / 6)).Nonempty
def CellTransported (Q : LevelCube 𝒮 M) (y : 𝒮.Point) (y' : Q.system.setting.Point) : Prop :=
  Q.system.embed '' 𝒮.cellOf y = Q.system.setting.cellOf y' ∧
    Q.system.setting.level y' = 𝒮.level y
def EndBlocksMeet (𝒯 : RegionSequence.NestedRegions) (j : ℕ) (c : 𝒯.BondAt j)
    (X : Set 𝒯.Point) : Prop :=
  ∃ x : 𝒯.FineSite, (x ∈ 𝒯.fineBlock j (c.source : 𝒯.Point) ∨
    x ∈ 𝒯.fineBlock j (c.target : 𝒯.Point)) ∧ (x : 𝒯.Point) ∈ X
def BondTransported (Q : LevelCube 𝒮 M) (j : ℕ) (c : 𝒮.BondAt j)
    (c' : Q.system.setting.BondAt j) : Prop :=
  (c'.source : Q.system.setting.Point) = Q.system.embed (c.source : 𝒮.Point) ∧
    c'.dir = c.dir
structure FirstTypePlacement (Q : LevelCube 𝒮 M) : Prop where
  alternative : (Q.enlarge 2 ∩ 𝒮.Ω (Q.level + 1) = ∅ ∧ 1 ≤ Q.level) ∨
    (Q.enlarge 2 ∩ 𝒮.Ω (Q.level + 1)).Nonempty
  inside : (Q.enlarge 2 ∩ 𝒮.Ω (Q.level + 1)).Nonempty → Q.enlarge 3 ⊆ 𝒮.Ω Q.level
  side_floor : (Q.enlarge 2 ∩ 𝒮.Ω (Q.level + 1)).Nonempty →
    26 * cubeSide 𝒮 M Q.level ≤ 𝒮.side
  corner : (Q.enlarge 2 ∩ 𝒮.Ω (Q.level + 1)).Nonempty → HasCornerCellInShell Q
  above : Q.enlarge 3 ∩ 𝒮.Ω (Q.level + 2) = ∅
  away : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) <
    supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0))
structure FirstTypeTransfer (Q : LevelCube 𝒮 M) : Prop where
  cell_levels : ∀ y ∈ 𝒮.allCentres, CellMeetsThicken Q y →
    y ∈ 𝒮.centresAt Q.level ∨ y ∈ 𝒮.centresAt (Q.level + 1)
  cell_inside : ∀ y ∈ 𝒮.allCentres, CellMeetsThicken Q y → 𝒮.cellOf y ⊆ Q.strictPts
  cell_carried : ∀ y ∈ 𝒮.allCentres, CellMeetsThicken Q y →
    ∃ y' ∈ Q.system.setting.allCentres, TorusCellMeetsThicken Q y' ∧ CellTransported Q y y'
  cell_onto : ∀ y' ∈ Q.system.setting.allCentres, TorusCellMeetsThicken Q y' →
    ∃ y ∈ 𝒮.allCentres, CellMeetsThicken Q y ∧ CellTransported Q y y'
  bond_levels : ∀ (j : ℕ) (c : 𝒮.BondAt j), c ∈ 𝒮.coarseBonds j →
    EndBlocksMeet 𝒮 j c (Q.thicken (2 / 3)) → j = Q.level ∨ j = Q.level + 1
  bond_carried : ∀ (j : ℕ) (c : 𝒮.BondAt j), c ∈ 𝒮.coarseBonds j →
    EndBlocksMeet 𝒮 j c (Q.thicken (2 / 3)) →
    ∃ c' ∈ Q.system.setting.coarseBonds j,
      EndBlocksMeet Q.system.setting j c' (Q.system.embed '' Q.thicken (2 / 3)) ∧
        BondTransported Q j c c'
  bond_onto : ∀ j : ℕ, j = Q.level ∨ j = Q.level + 1 →
    ∀ c' ∈ Q.system.setting.coarseBonds j,
      EndBlocksMeet Q.system.setting j c' (Q.system.embed '' Q.thicken (2 / 3)) →
      ∃ c ∈ 𝒮.coarseBonds j, EndBlocksMeet 𝒮 j c (Q.thicken (2 / 3)) ∧ BondTransported Q j c c'
  laplacian_agrees : ∀ f ∈ 𝒮.siteFns, VanishesOff (Q.thicken (2 / 3)) f →
    CubeTorus.SiteFunctionsMatch Q (dirichletLap f)
      (latticeLaplacian (CubeTorus.restrictSites Q f))
  gradient_agrees : ∀ f ∈ 𝒮.siteFns, VanishesOff (Q.thicken (2 / 3)) f →
    CubeTorus.BondFunctionsMatch Q (dDir f) (dTorus (CubeTorus.restrictSites Q f))
  gradient_adjoint_agrees : ∀ A ∈ 𝒮.oneForms, AnchorSupported (Q.thicken (2 / 3)) A →
    CubeTorus.SiteFunctionsMatch Q (dDirAdj A) (dTorusAdj (CubeTorus.restrictBonds Q A))
  curl_agrees : ∀ A ∈ 𝒮.oneForms, AnchorSupported (Q.thicken (2 / 3)) A →
    CubeTorus.BondFunctionsMatch Q (curlSqDir A)
      (curlTorusAdj (curlTorus (CubeTorus.restrictBonds Q A)))
  averaging_term_agrees : ∀ f ∈ 𝒮.siteFns, VanishesOff (Q.thicken (2 / 3)) f →
    CubeTorus.SiteFunctionsMatch Q (CubeTorus.averagingOp f)
      (CubeTorus.averagingOp (CubeTorus.restrictSites Q f))
  averaged_operator_agrees : ∀ A ∈ 𝒮.oneForms, AnchorSupported (Q.thicken (2 / 3)) A →
    CubeTorus.BondFunctionsMatch Q (avgOp A) (avgOp (CubeTorus.restrictBonds Q A))
variable (𝒮 M)
structure PartitionOfUnityBounds (c : ℝ) : Prop where
  sum_squares : ∀ x : 𝒮.Point, ∑ n ∈ Finset.range (topLevel 𝒮 + 1),
    ∑ᶠ Q ∈ {Q : LevelCube 𝒮 M | Q.level = n}, Q.partitionFn x ^ 2 = 1
  sum_squares_at_bonds : ∀ b ∈ 𝒮.bonds,
    ∑ᶠ Q ∈ active 𝒮 M, Q.partitionFn (b.source : 𝒮.Point) ^ 2 = 1
  partition_bounded : ∀ Q : LevelCube 𝒮 M,
    IsScaleBounded c (mollifyRadius 𝒮 M Q.level) Q.partitionFn
  inner_bounded : ∀ Q : LevelCube 𝒮 M,
    IsScaleBounded c (mollifyRadius 𝒮 M Q.level) Q.smallCutoff
  outer_bounded : ∀ Q : LevelCube 𝒮 M,
    IsScaleBounded c (mollifyRadius 𝒮 M Q.level) Q.largeCutoff
structure Placement : Prop where
  near_centre : ∀ Q ∈ active 𝒮 M, Q.thicken (5 / 6) ⊆
    {x | supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level}
  away_from_complement : ∀ Q ∈ active 𝒮 M, 1 ≤ Q.level → Q.thicken (5 / 6) ⊆
    {x | ENNReal.ofReal (1 / 6 * mollifyRadius 𝒮 M Q.level) ≤ distToOutside 𝒮 Q.level x}
  near_next_complement : ∀ Q ∈ active 𝒮 M, Q.thicken (5 / 6) ⊆
    {x | distToOutside 𝒮 (Q.level + 1) x ≤
      ENNReal.ofReal (1 / 2 * cubeSide 𝒮 M Q.level)}
  in_interior : ∀ Q ∈ active 𝒮 M, Q.thicken (5 / 6) ⊆ Q.strictPts
  in_layers : ∀ Q ∈ active 𝒮 M, (1 ≤ Q.level ∨ Q.pts ⊆ 𝒮.Ω 0) →
    Q.thicken (5 / 6) ⊆ 𝒮.shellOf Q.level ∪ 𝒮.shellOf (Q.level + 1)
  near_level : ∀ (m : ℕ), ∀ y ∈ 𝒮.centresAt m, ∀ Q ∈ activeNear 𝒮 M y,
    Q.level + 1 = m ∨ Q.level = m
  near_thickened : ∀ (m : ℕ), ∀ y ∈ 𝒮.centresAt m, ∀ Q ∈ activeNear 𝒮 M y,
    y ∈ Q.thicken (1 / 6)
  near_count : ∀ (m : ℕ), ∀ y ∈ 𝒮.centresAt m, (activeNear 𝒮 M y).encard ≤ 2 ^ (4 + 1)
  corner_in_layer : ∀ Q ∈ active 𝒮 M, 1 ≤ Q.level → HasCornerCellInShell Q
  in_previous : ∀ Q ∈ active 𝒮 M, 1 ≤ Q.level → Q.pts ⊆ 𝒮.Ω (Q.level - 1)
  first_kind : ∀ Q : LevelCube 𝒮 M, Q.IsFirstType → FirstTypePlacement Q
  second_kind : ∀ Q : LevelCube 𝒮 M, Q.IsSecondType →
    ENNReal.ofReal (2 * (M : ℝ) * 𝒮.ξ) ≤ supSetDist Q.pts (𝒮.Ω 1)
structure WeightedDistComparisons : Prop where
  to_centre : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.Ω 0 →
    𝒮.weightedDist (x : 𝒮.Point) (𝒮.centreOfSite x) ≤ 1 / 2 * 4
  centre_near : ∀ (m : ℕ), ∀ y ∈ 𝒮.centresAt m, ∀ x : 𝒮.FineSite,
    (x : 𝒮.Point) ∈ cubeHalfSide y (2 * 𝒮.levelScale y) → (x : 𝒮.Point) ∈ 𝒮.Ω 0 →
    𝒮.weightedDist y (𝒮.centreOfSite x) ≤ 3 * 4 * (𝒮.L : ℝ)
  level_near : ∀ (m : ℕ), ∀ y ∈ 𝒮.centresAt m, ∀ x : 𝒮.FineSite,
    (x : 𝒮.Point) ∈ cubeHalfSide y (2 * 𝒮.levelScale y) → (x : 𝒮.Point) ∈ 𝒮.Ω 0 →
    |(𝒮.level (𝒮.centreOfSite x) : ℤ) - (m : ℤ)| ≤ 1
  in_cube : ∀ Q ∈ active 𝒮 M, ∀ x x' : 𝒮.FineSite,
    (x : 𝒮.Point) ∈ Q.strictPts → (x' : 𝒮.Point) ∈ Q.strictPts →
    𝒮.weightedDist (x : 𝒮.Point) (x' : 𝒮.Point) ≤
      (𝒮.L : ℝ) * Q.torusDist (Q.system.embed x) (Q.system.embed x')
  local_distance_le : ∀ Q ∈ active 𝒮 M, ∀ x x' : 𝒮.FineSite,
    (x : 𝒮.Point) ∈ Q.strictPts → (x' : 𝒮.Point) ∈ Q.strictPts →
    Q.torusDist (Q.system.embed x) (Q.system.embed x') ≤ 2 * 4 * (M : ℝ)
  across_a_ball : ∀ (r : ℝ) (j : ℕ) (x : 𝒮.Point), 0 < r → r < 𝒮.side / 2 →
    {x' | supNorm (x' - x) < r} ∩ 𝒮.Ω (j + 1) = ∅ →
    ∀ x' : 𝒮.Point, r ≤ supNorm (x - x') → r / 𝒮.scale j ≤ 𝒮.weightedDist x x'
  out_of_a_cube : ∀ Q : LevelCube 𝒮 M, Q.IsFirstType → ∀ y'' ∈ 𝒮.allCentres,
    (𝒮.cellOf y'' ∩ Q.supp).Nonempty → ∀ y ∈ 𝒮.allCentres, ¬𝒮.cellOf y ⊆ Q.thicken (1 / 6) →
    (M : ℝ) / (72 * (𝒮.L : ℝ) ^ 2) ≤ 𝒮.weightedDist y y''
structure GeometryHolds (c : ℝ) : Prop where
  partition : PartitionOfUnityBounds 𝒮 M c
  positions : Placement 𝒮 M
  agreement : ∀ Q : LevelCube 𝒮 M, Q.IsFirstType → FirstTypeTransfer Q
  distance : WeightedDistComparisons 𝒮 M
variable {𝒮 M}
def IsGeometryConstant (c : ℝ) : Prop :=
  1 ≤ c ∧ ∀ (K m M R₁ : ℕ) (𝒮 : RegionSequence.NestedRegions), 𝒮.IsLevelUnitChain K m M R₁ →
    𝒮.L ^ 5 ≤ M → GeometryHolds 𝒮 M c
def geometryConstant : ℝ := Classical.epsilon IsGeometryConstant
def GeometryStatement : Prop := IsGeometryConstant geometryConstant
end PartitionCubes.CubeGeometry
end YangMills.Construction
