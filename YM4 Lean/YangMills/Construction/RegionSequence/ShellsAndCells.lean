import YangMills.Construction.RegionSequence.PastLastLevel
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence
structure ShellCells (𝒮 : NestedRegions) : Prop where
  regions_cubeUnion : ∀ j ≤ 𝒮.s, 𝒮.IsCubeUnionAt j (𝒮.Ω j) ∧ 𝒮.IsCubeUnionAt j (𝒮.Ω (j + 1))
  shellOf_eq : ∀ j ≤ 𝒮.s,
    𝒮.shellOf j = ⋃₀ {Q ∈ 𝒮.cubePartitionAt j | Q ⊆ 𝒮.Ω j ∧ ¬ Q ⊆ 𝒮.Ω (j + 1)}
  shellCubes_eq : ∀ j ≤ 𝒮.s,
    {Q ∈ 𝒮.cubePartitionAt j | Q ⊆ 𝒮.Ω j ∧ ¬ Q ⊆ 𝒮.Ω (j + 1)} = 𝒮.cellOf '' 𝒮.centresAt j
  interior_disjoint_next : ∀ j ≤ 𝒮.s,
    ∀ Q ∈ {Q ∈ 𝒮.cubePartitionAt j | Q ⊆ 𝒮.Ω j ∧ ¬ Q ⊆ 𝒮.Ω (j + 1)},
      Disjoint (interior Q) (𝒮.Ω (j + 1))
  cellOf_subset : ∀ j ≤ 𝒮.s, ∀ y ∈ 𝒮.centresAt j, 𝒮.cellOf y ⊆ 𝒮.shellOf j ∧
    𝒮.shellOf j ⊆ 𝒮.Ω j ∩ 𝒮.cubeComplementAt j (𝒮.Ω (j + 1))
  pairwise_interior_disjoint : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, y ≠ y' →
    Disjoint (interior (𝒮.cellOf y)) (interior (𝒮.cellOf y'))
  iUnion_cellOf : ⋃ y ∈ 𝒮.allCentres, 𝒮.cellOf y = 𝒮.Ω 0
  fineSite_mem_unique : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.Ω 0 → ∃ y ∈ 𝒮.allCentres,
    (x : 𝒮.Point) ∈ interior (𝒮.cellOf y) ∧
      ∀ y' ∈ 𝒮.allCentres, (x : 𝒮.Point) ∈ 𝒮.cellOf y' → y' = y
end YangMills.Construction.RegionSequence
