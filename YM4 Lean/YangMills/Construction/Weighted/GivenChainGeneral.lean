import YangMills.Construction.Torus.PartitionsShellsCubes
import YangMills.Construction.Weighted.BareLatticeBonds
import YangMills.Construction.Weighted.GivenChain
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
def segmentToLifted (s : Torus.TorusSegment 4) : TorusMetric.LiftedSegment :=
  ⟨s.start, s.start + s.direction⟩
namespace GivenChainGeneral
structure ScaleLatticePartition (D : TorusData) (i : ℕ) : Prop where
  ratio_even : Torus.IsPosEvenNat (D.side / D.scale i)
  latticeAt_eq : D.latticeAt (D.scale i) =
    (Torus.spacingLattice 4 D.side (Torus.scaleSpacing D.L D.bareSpacing i) :
      Set (Torus.PeriodicTorus 4 D.side))
  partitionAt_eq : D.partitionAt (D.scale i) =
    Torus.cubePartition 4 D.side (Torus.scaleSpacing D.L D.bareSpacing i)
structure SpaceIsPeriodicTorus (D : TorusData) : Prop where
  space_eq : D.Space = Torus.PeriodicTorus 4 D.side
  scale_data : ∀ i : ℕ, D.scale i ≤ (D.blockNumber : ℝ) * D.scale D.top →
    ScaleLatticePartition D i
  proj_facts : Torus.ProjectionFacts 4 D.side
  nested : ∀ i' i : ℕ, i' ≤ i → D.scale i ≤ (D.blockNumber : ℝ) * D.scale D.top →
    Torus.NestedPartitionFacts 4 D.L D.bareSpacing D.side (Torus.scaleSpacing D.L D.bareSpacing i)
      (Torus.scaleSpacing D.L D.bareSpacing i')
  side_ge : ∀ n ≤ D.top, 2 * (D.blockNumber : ℝ) * D.scale n ≤ D.side ∧
    2 * (D.L : ℝ) * D.scale n ≤ 2 * (D.blockNumber : ℝ) * D.scale n
variable {D : TorusData} (B : SeparatedChain D)
structure AgreesWithGeneral : Prop where
  isSeparated : Torus.IsSeparatedChain (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber
    D.gapNumber D.top B.stage
  layer_eq_shell : ∀ n ≤ D.top, B.layer n = Torus.shell (d := 4) (S := D.side) B.stage n
  layerSites_eq_shellSites : ∀ n ≤ D.top, B.layerSites n =
    Torus.shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n
  allSites_eq_union : B.allSites =
    Torus.unionShellSites (d := 4) (S := D.side) D.L D.bareSpacing D.top B.stage
  siteScale_eq : ∀ y ∈ B.allSites, B.siteScale y =
    Torus.shellSpacing (d := 4) (S := D.side) D.L D.bareSpacing B.stage y
  siteCube_eq_cube : ∀ y ∈ B.allSites, B.siteCube y =
    Torus.siteCube (d := 4) (S := D.side) D.L D.bareSpacing B.stage y
  weightedLength_eq_general : ∀ Γ : List (Torus.TorusSegment 4),
    B.weightedLength (Γ.map segmentToLifted) =
      Torus.chainWeightedLength (d := 4) (S := D.side) D.L D.bareSpacing D.top B.stage Γ
  weightedDistance_eq_general : ∀ x x' : D.Space, B.weightedDistance x x' =
    Torus.chainWeightedDist (d := 4) (S := D.side) D.L D.bareSpacing D.top B.stage x x'
structure ShellsAndCubes : Prop where
  layer_isCubeUnion : ∀ n ≤ D.top,
    D.IsCubeUnionAt ((D.blockNumber : ℝ) * D.scale n) (B.layer n)
  layer_eq_iUnion : ∀ n ≤ D.top, B.layer n = ⋃ y ∈ B.layerSites n, B.siteCube y
  layer_subset_diff : ∀ n ≤ D.top, B.layer n ⊆ B.stage n ∩ D.closedComplement (B.stage (n + 1))
  closedComplement_mono : ∀ m m' : ℕ, m ≤ m' →
    D.closedComplement (B.stage m) ⊆ D.closedComplement (B.stage m')
  iUnion_siteCube_eq : ⋃ y ∈ B.allSites, B.siteCube y = B.stage 0
  interior_disjoint_succ : ∀ n, ∀ y ∈ B.layerSites n,
    Disjoint (interior (B.siteCube y)) (B.stage (n + 1))
  interior_disjoint_layer : ∀ n, ∀ y ∈ B.layerSites n, ∀ m, m ≠ n →
    Disjoint (interior (B.siteCube y)) (B.layer m)
  interior_disjoint_cube : ∀ n, ∀ y ∈ B.layerSites n, ∀ y' ∈ B.allSites, y' ≠ y →
    Disjoint (interior (B.siteCube y)) (B.siteCube y')
structure SiteBlockGrid (n : ℕ) (y : D.Space) (z : Fin 4 → ℝ) : Prop where
  isGrid : Torus.IsCenteredGrid D.side (D.scale 0) ((D.L : ℝ) ^ n) z (Subtype.val '' B.block y)
  card_eq : (D.L : ℝ) ^ (n * 4) = (B.siteScale y / D.scale 0) ^ 4
  mem_interior : ∀ x ∈ B.block y, (x : D.Space) ∈ interior (B.siteCube y)
  adjacent_iff : ∀ k ∈ Torus.centredIntVectors 4 ((D.L : ℝ) ^ n),
    ∀ k' ∈ Torus.centredIntVectors 4 ((D.L : ℝ) ^ n),
    ∀ x x' : D.BareSite,
      (x : D.Space) = Torus.gridImage D.side (D.scale 0) z k →
      (x' : D.Space) = Torus.gridImage D.side (D.scale 0) z k' →
      (TorusData.Adjacent x x' ↔ ∃ μ, k' = k + Pi.single μ 1 ∨ k' = k - Pi.single μ 1)
structure BlockPartition : Prop where
  block_nonempty : ∀ y ∈ B.allSites, (B.block y).Nonempty
  block_pairwise_disjoint : ∀ y ∈ B.allSites, ∀ y' ∈ B.allSites, y ≠ y' →
    Disjoint (B.block y) (B.block y')
  iUnion_block : ⋃ y ∈ B.allSites, B.block y = D.bareSites (B.stage 0)
  cubeAround_subset : ∀ x ∈ D.bareSites (B.stage 0),
    D.cubeAround (D.scale 0) (x : D.Space) ⊆ B.siteCube (B.blockCenter x)
  sitesIn_iUnion : ∀ Y ⊆ B.allSites, Y = B.sitesIn (⋃ y ∈ Y, B.siteCube y)
  bareSites_iUnion : ∀ Y ⊆ B.allSites,
    D.bareSites (⋃ y ∈ Y, B.siteCube y) = ⋃ y ∈ Y, B.block y
  card_bondsAtSite : ∀ x : D.BareSite, (TorusData.bondsAtSite x).ncard = 2 * 4
end GivenChainGeneral
open GivenChainGeneral in
def GivenChainGeneralFacts : Prop :=
  ∀ G : GivenChain,
    SpaceIsPeriodicTorus G.data ∧ AgreesWithGeneral G.chain ∧ ShellsAndCubes G.chain ∧
    (∀ n, ∀ y ∈ G.chain.layerSites n, ∀ z : Fin 4 → ℝ, Torus.torusProj 4 G.data.side z = y →
      SiteBlockGrid G.chain n y z) ∧
    BlockPartition G.chain ∧
    ∀ x x' x'' : G.data.Space, G.chain.weightedDistance x x'' ≤
      G.chain.weightedDistance x x' + G.chain.weightedDistance x' x''
end YangMills.Construction.Weighted
end
