import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace LevelUnitPartition
variable (S : LevelUnitPartition)
def IsLevelDomain (X : Set S.Points) : Prop :=
  X ∈ connectedRegions S.params.L S.params.m S.index ∨
    X ∈ faceChainConnectedRegions S.params.L S.params.m S.index
def IsAdmissibleTargetFamily (X : Set S.Points) (G : Set (Set S.Points)) : Prop :=
  S.IsLevelDomain X ∧ G.Finite ∧ (∀ A ∈ G, IsPartitionRegion S.index A) ∧
    ∃ Γ, IsSpanningEdgeTree S.index X G Γ
def minTreeEdges (X : Set S.Points) (G : Set (Set S.Points)) : ℕ :=
  sInf {e | ∃ Γ, IsSpanningEdgeTree S.index X G Γ ∧ (S.graphEdges Γ).ncard = e}
def RelativeEdgeSizeDefined (Z X : Set S.Points) : Prop :=
  S.IsLevelDomain X ∧ IsPartitionRegion S.index Z ∧
    ((cubesNotIn S.index X Z).Nonempty →
      S.IsAdmissibleTargetFamily X (cubesNotIn S.index X Z))
open Classical in
def relativeEdgeSize (Z X : Set S.Points) : ℕ :=
  if (cubesNotIn S.index X Z).Nonempty then
    S.minTreeEdges X (cubesNotIn S.index X Z)
  else 0
def IslandEdgeLengthDefined (I : Set (Set S.Points)) (X : Set S.Points) : Prop :=
  IsIslandCollection S.index I ∧ ¬X ⊆ ⋃₀ I ∧
    S.IsAdmissibleTargetFamily X (islandTreeTargets S.index I X)
def islandEdgeLength (I : Set (Set S.Points)) (X : Set S.Points) : ℕ :=
  S.minTreeEdges X (islandTreeTargets S.index I X)
def IsMinimalEdgeTree (I : Set (Set S.Points)) (X Γ : Set S.Points) : Prop :=
  S.IslandEdgeLengthDefined I X ∧ IsSpanningEdgeTree S.index X (islandTreeTargets S.index I X) Γ ∧
    (S.graphEdges Γ).ncard = S.islandEdgeLength I X
end LevelUnitPartition
end PeriodicLattice
end YangMills.Construction
end
