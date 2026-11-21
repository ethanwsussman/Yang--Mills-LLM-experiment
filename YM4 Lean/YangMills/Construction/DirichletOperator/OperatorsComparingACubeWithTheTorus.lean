import YangMills.Construction.DirichletOperator.BoundsOnTheToriOfTheCubes
import YangMills.Construction.PartitionCubes.CubeTorusTransfer
import YangMills.Construction.RegionSequence.GaugeConditionProjections
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeTorus (torusSetting levelSpacing)
noncomputable section
namespace YangMills.Construction.CubeTorusComparison
variable {𝒮 : NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M)
def cutoffPush (f : (torusSetting Q).FineSite → ℝ) : 𝒮.FineSite → ℝ :=
  Q.system.pushSites Q.largeCutoff f
def cutoffPull (g : 𝒮.FineSite → ℝ) : (torusSetting Q).FineSite → ℝ :=
  Q.system.pullSites Q.largeCutoff g
open Classical in
def coarsePush (ω : (torusSetting Q).Coarse) : 𝒮.Coarse :=
  fun y => if h : Q.system.embed y ∈ (torusSetting Q).allCentres then
    Q.largeCutoff y * ω ⟨Q.system.embed y, h⟩ else 0
def coarsePull (ω : 𝒮.Coarse) : (torusSetting Q).Coarse :=
  fun w => ∑ᶠ y ∈ {y : 𝒮.allCentres | (y : 𝒮.Point) ∈ tsupport Q.largeCutoff ∧
    Q.system.embed y = w}, Q.largeCutoff y * ω y
def pushLapCommutator (f : (torusSetting Q).FineSite → ℝ) : 𝒮.FineSite → ℝ :=
  cutoffPush Q (gaugeLap f) - gaugeLap (cutoffPush Q f)
def pushAvgDefect (ω : (torusSetting Q).Coarse) : 𝒮.FineSite → ℝ :=
  cutoffPush Q (blockAvgAdj ω) - blockAvgAdj (coarsePush Q ω)
def pullLapCommutator (g : 𝒮.FineSite → ℝ) : (torusSetting Q).FineSite → ℝ :=
  cutoffPull Q (gaugeLap g) - gaugeLap (cutoffPull Q g)
def pullAvgDefect (ω : 𝒮.Coarse) : (torusSetting Q).FineSite → ℝ :=
  cutoffPull Q (blockAvgAdj ω) - blockAvgAdj (coarsePull Q ω)
def cellAndNeighbours (u : 𝒮.FineSite) : Set 𝒮.FineSite :=
  {u' | (u' : 𝒮.Point) ∈ 𝒮.cellOf (𝒮.centreOfSite u) ∨ IsNeighbor u u'}
def nonconstantCells : Set 𝒮.Point :=
  {y | y ∈ 𝒮.allCentres ∧ ∃ u : 𝒮.FineSite, (u : 𝒮.Point) ∈ 𝒮.cellOf y ∧
    ∃ u' ∈ cellAndNeighbours u, Q.largeCutoff (u' : 𝒮.Point) ≠ Q.largeCutoff (u : 𝒮.Point)}
def InNonconstantCell (u : 𝒮.FineSite) : Prop :=
  ∃ y ∈ nonconstantCells Q, (u : 𝒮.Point) ∈ 𝒮.cellOf y
def bondDivergence (J : 𝒮.FineBond → ℝ) : (torusSetting Q).FineSite → ℝ :=
  dDirAdj (YangMills.Construction.PartitionCubes.CubeTorus.restrictBonds Q J)
def cellCountBound (M : ℕ) : ℝ := (8 * (M : ℝ)) ^ 4
structure LargeEnough (L K m M R₁ : ℕ) (𝒮 : NestedRegions) : Prop where
  blocking : 𝒮.L = L
  sequence : 𝒮.IsLevelUnitChain K m M R₁
  block_floor : max (max ((L : ℝ) ^ 5)
      ((L : ℝ) * (YangMills.Construction.CubeTorus.chosenConstants L).minBlock))
    (RegionSequence.OperatorEstimates.chosenConstants L).minBlock ≤ (M : ℝ)
  product_floor : max (RegionSequence.OperatorEstimates.chosenConstants L).minProduct
    (Weighted.separatedSumRadius 4 L (1 / 16 * (RegionSequence.OperatorEstimates.chosenConstants L).δ)) ≤
      (R₁ : ℝ) * (M : ℝ)
end YangMills.Construction.CubeTorusComparison
