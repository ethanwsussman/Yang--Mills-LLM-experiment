import YangMills.Construction.RegionSequence.PastLastLevel
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence
structure CubePartitions (𝒮 : NestedRegions) : Prop where
  frontier_mem_halfPlanes : ∀ i, 𝒮.IsPartitionLevel i → ∀ Q ∈ 𝒮.cubePartitionAt i,
    ∀ p ∈ frontier Q, ∃ (μ : Fin 4) (k : ℤ),
      p μ = ((((k : ℝ) + 1 / 2) * 𝒮.scale i : ℝ) : AddCircle 𝒮.side)
  cube_eq_sUnion_finer : ∀ i i', i ≤ i' → 𝒮.IsPartitionLevel i' → ∀ Q ∈ 𝒮.cubePartitionAt i',
    Q = ⋃₀ {Q' ∈ 𝒮.cubePartitionAt i | Q' ⊆ Q}
  site_mem_interior_unique : ∀ i i', i ≤ i' → 𝒮.IsPartitionLevel i' →
    ∀ x ∈ YangMills.Construction.Torus.spacingLattice 4 𝒮.side (𝒮.scale i),
      ∃ Q ∈ 𝒮.cubePartitionAt i', x ∈ interior Q ∧
        ∀ Q' ∈ 𝒮.cubePartitionAt i', x ∈ Q' → Q' = Q
  cubeComplementAt_eq_closure : ∀ i', 𝒮.IsPartitionLevel i' → ∀ X, 𝒮.IsCubeUnionAt i' X →
    𝒮.cubeComplementAt i' X = closure Xᶜ
  cubeComplementAt_finer : ∀ i i', i ≤ i' → 𝒮.IsPartitionLevel i' → ∀ X,
    𝒮.IsCubeUnionAt i' X →
      𝒮.IsCubeUnionAt i X ∧ 𝒮.cubeComplementAt i X = 𝒮.cubeComplementAt i' X
  fineBlock_eq : ∀ n ≤ 𝒮.s,
    ∀ y ∈ YangMills.Construction.Torus.spacingLattice 4 𝒮.side (𝒮.scale n),
      {x : 𝒮.FineSite | (x : 𝒮.Point) ∈ YangMills.Construction.Torus.cubeAt y (𝒮.scale n)} =
          𝒮.fineBlock n y ∧
        (𝒮.fineBlock n y).ncard = 𝒮.L ^ (n * 4)
end YangMills.Construction.RegionSequence
