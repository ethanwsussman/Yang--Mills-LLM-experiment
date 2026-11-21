import YangMills.Construction.Lattice.EdgeGraphsInLargerRegions
import YangMills.Construction.Lattice.EdgeGraphsThatAreNotEmpty
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.PeriodicLattice.RegionMonotonicity
variable (S : LevelUnitPartition)
theorem isEdgeGraph_of_cubes_subset (hgraphs : EdgeGraphsDescribedByCubes) {X Y : Set S.Points}
    (hX : IsPartitionRegion S.index X) (hY : IsPartitionRegion S.index Y)
    (hXY : partitionCubesIn S.index X ⊆ partitionCubesIn S.index Y) {Γ : Set S.Points}
    (hΓ : Γ.Nonempty) (hG : S.IsEdgeGraphInRegion X Γ) : S.IsEdgeGraphInRegion Y Γ := by
  obtain ⟨hdesc, hcorner, hedges⟩ := (hgraphs S Y hY).1
  rcases (hgraphs S X hX).1.1 Γ hG hΓ with ⟨Δ, hΔ, v, hv, rfl⟩ | ⟨E, -, hE, hmem, rfl⟩
  · exact hcorner Δ (hXY hΔ) v hv
  · refine hedges E hE fun e he => ?_
    obtain ⟨Δ, hΔ, hee⟩ := hmem e he
    exact ⟨Δ, hXY hΔ, hee⟩
theorem isEdgeTree_of_cubes_subset (hgraphs : EdgeGraphsDescribedByCubes) {X Y : Set S.Points}
    (hX : IsPartitionRegion S.index X) (hY : IsPartitionRegion S.index Y)
    (hXY : partitionCubesIn S.index X ⊆ partitionCubesIn S.index Y) {Γ : Set S.Points}
    (hT : S.IsEdgeTreeInRegion X Γ) : S.IsEdgeTreeInRegion Y Γ :=
  ⟨isEdgeGraph_of_cubes_subset S hgraphs hX hY hXY hT.2.nonempty hT.1, hT.2⟩
theorem isPartitionRegion_fullRegion : IsPartitionRegion S.index S.fullRegion :=
  ⟨S.cubes, subset_rfl, rfl⟩
theorem partitionCubesIn_subset_fullRegion (X : Set S.Points) :
    partitionCubesIn S.index X ⊆ partitionCubesIn S.index S.fullRegion :=
  fun _ hQ => ⟨hQ.1, subset_sUnion_of_mem hQ.1⟩
theorem edgeGraphsExtendToLargerRegions_holds (hgraphs : EdgeGraphsDescribedByCubes) :
    EdgeGraphsExtendToLargerRegions := by
  intro S
  refine ⟨fun X Y hX hY hXY =>
    ⟨fun Γ hΓ hG => isEdgeGraph_of_cubes_subset S hgraphs hX hY hXY hΓ hG,
    fun Γ hT => isEdgeTree_of_cubes_subset S hgraphs hX hY hXY hT⟩,
    fun X hX => ⟨fun Γ hΓ hG => ?_, fun Γ hT => ?_⟩⟩
  · exact isEdgeGraph_of_cubes_subset S hgraphs hX (isPartitionRegion_fullRegion S)
      (partitionCubesIn_subset_fullRegion S X) hΓ hG
  · exact isEdgeTree_of_cubes_subset S hgraphs hX (isPartitionRegion_fullRegion S)
      (partitionCubesIn_subset_fullRegion S X) hT
end YangMills.Construction.PeriodicLattice.RegionMonotonicity
