import YangMills.Construction.Lattice.AdjacentVerticesAndConnectedEdgeGraphs
import YangMills.Construction.Lattice.EdgeGraphsMeetCubesAtTheirVertices
import YangMills.Construction.Lattice.EdgeGraphsThatAreNotEmpty
import YangMills.Construction.Lattice.EdgesOfAPartitionAndTheirEndPoints
import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdges
import YangMills.Construction.Lattice.NumberingOfVerticesAlongEdges
import YangMills.Construction.Lattice.VerticesAndCornersOfCubesOfAPartition
import YangMills.Construction.Lattice.VerticesAndCubesOfAConnectedEdgeGraph
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace EdgeGraphVertexCount
open EdgeGraphCubeProperties CubeLifts
variable (P : LevelUnitPartition)
theorem encard_biUnion_le_sixteen_mul {α β : Type} {W : Set α} (hW : W.Finite) (f : α → Set β)
    (hf : ∀ v ∈ W, (f v).encard ≤ 16) : (⋃ v ∈ W, f v).encard ≤ 16 * W.encard := by
  induction W, hW using Set.Finite.induction_on with
  | empty => simp
  | @insert a s ha hs ih =>
    rw [biUnion_insert, encard_insert_of_notMem ha]
    calc (f a ∪ ⋃ v ∈ s, f v).encard ≤ (f a).encard + (⋃ v ∈ s, f v).encard :=
          encard_union_le _ _
      _ ≤ 16 + 16 * s.encard :=
          add_le_add (hf a (mem_insert _ _)) (ih fun v hv => hf v (mem_insert_of_mem _ hv))
      _ = 16 * (s.encard + 1) := by ring
theorem add_side_smul_coordVec_mem_vertexSet {w : Fin 4 → ℝ} (hw : w ∈ P.vertexSet) (ν : Fin 4) :
    w + (P.side : ℝ) • coordVec ν ∈ P.vertexSet := by
  intro μ
  obtain ⟨a, ha⟩ := hw μ
  by_cases h : μ = ν
  · subst h
    refine ⟨a + 1, ?_⟩
    simp [coordVec, ha]
    ring
  · refine ⟨a, ?_⟩
    simp [coordVec, ha, h]
theorem isVertex_of_isEdgeEndpoint (hL : CubeLifts.Statement)
    {e : Set P.Points} {v : P.Points} (h : P.IsEdgeEndpoint e v) : P.IsVertex v := by
  obtain ⟨-, -, -, hV, -, -⟩ := hL.2.2 P
  obtain ⟨w, hw, ν, -, rfl | rfl⟩ := h
  · exact (hV.1 _).2 ⟨w, hw, rfl⟩
  · exact (hV.1 _).2 ⟨_, add_side_smul_coordVec_mem_vertexSet P hw ν, rfl⟩
theorem isVertex_of_mem_graphVertices (hL : CubeLifts.Statement)
    {Γ : Set P.Points} {v : P.Points} (hv : v ∈ P.graphVertices Γ) : P.IsVertex v := by
  rcases hv with ⟨e, -, h⟩ | ⟨h, -⟩
  · exact isVertex_of_isEdgeEndpoint P hL h
  · exact h
end EdgeGraphVertexCount
open EdgeGraphVertexCount EdgeGraphCubeProperties CubeLifts in
theorem connectedEdgeGraphVerticesAndCubes_holds (hL : CubeLifts.Statement)
    (hG : EdgeGraphsDescribedByCubes) (hE : PartitionEdgeEndpoints)
    (hC : PartitionCubeVertexCornerIncidence)
    (hM : EdgeGraphsMeetCubesAtVertices)
    (hA : AdjacentVerticesConnectEdgeGraphs)
    (hN : VerticesNumberedAlongEdges) :
    ConnectedEdgeGraphVerticesAndCubes := by
  intro P e Γ hΓ hconn hcount
  obtain ⟨hT, -, -, hV, -, -⟩ := hL.2.2 P
  have hpart : P.cubes = standardCubePartition P.params.L P.params.m P.index := hT.2.2.1
  have hX : IsPartitionRegion P.index P.fullRegion := ⟨P.cubes, hpart.subset, rfl⟩
  have hne : Γ.Nonempty := hconn.nonempty
  obtain ⟨-, hTwo, -, hUnion, hCorner, -⟩ := hE P P.fullRegion hX
  have hVfin : (P.graphVertices Γ).Finite :=
    hV.2.2.2.1.subset fun v h => isVertex_of_mem_graphVertices P hL h
  have hvert : (P.graphVertices Γ).encard ≤ (e : ℕ∞) + 1 := by
    rcases (hG P P.fullRegion hX).1.1 Γ hΓ hne with ⟨Q, hQ, v, hv, rfl⟩ | ⟨E, hEf, hEn, hEe, rfl⟩
    · have hQp : Q ∈ P.cubes := by
        rw [hpart]
        exact hQ.1
      have h0 := hCorner v ⟨Q, hQp, hv⟩
      have hsub : P.graphVertices {v} ⊆ {v} := by
        rintro u (⟨a, ha, -⟩ | ⟨-, h⟩)
        · rw [h0] at ha
          exact ha.elim
        · exact (singleton_injective h).symm
      calc (P.graphVertices {v}).encard ≤ ({v} : Set P.Points).encard := encard_le_encard hsub
        _ = 1 := encard_singleton v
        _ ≤ (e : ℕ∞) + 1 := le_add_self
    · have hEp : ∀ a ∈ E, P.IsEdge a := fun a ha => by
        obtain ⟨Q, hQ, h⟩ := hEe a ha
        refine ⟨Q, ?_, h⟩
        rw [hpart]
        exact hQ.1
      obtain ⟨h1, -⟩ := hUnion (⋃₀ E) E hΓ hEf hEn hEp rfl
      have hWend : ∀ a ∈ E, ∀ v, P.IsEdgeEndpoint a v → v ∈ P.graphVertices (⋃₀ E) :=
        fun a ha v hv => Or.inl ⟨a, by rw [h1]; exact ha, hv⟩
      obtain ⟨a₀, ha₀⟩ := hEn
      have hpts : {v | P.IsEdgeEndpoint a₀ v}.Nonempty :=
        nonempty_of_ncard_ne_zero (by rw [hTwo a₀ (hEp a₀ ha₀)]; norm_num)
      obtain ⟨F, hF⟩ := hpts
      have hFW : F ∈ P.graphVertices (⋃₀ E) := hWend a₀ ha₀ F hF
      have hq : 1 ≤ (P.graphVertices (⋃₀ E)).ncard :=
        (ncard_pos hVfin).2 ⟨F, hFW⟩
      obtain ⟨-, -, hUn, -⟩ := hA P
      have hjoin := ((hUn E hEf ⟨a₀, ha₀⟩ hEp).2).1 hconn
      rw [h1] at hjoin
      obtain ⟨v, -, -, a, ha, hinj, -⟩ := hN P (P.graphVertices (⋃₀ E)) _ E hVfin rfl hq
        (fun v h => isVertex_of_mem_graphVertices P hL h)
        (fun b hb => ⟨hEp b hb, hWend b hb⟩) hjoin F hFW
      have himg : a '' Icc 2 (P.graphVertices (⋃₀ E)).ncard ⊆ E := by
        rintro _ ⟨k, hk, rfl⟩
        exact (ha k hk.1 hk.2).1
      have hle := encard_le_encard himg
      rw [hinj.encard_image, ← Finset.coe_Icc, encard_coe_eq_coe_finsetCard, Nat.card_Icc] at hle
      rw [h1] at hcount
      rw [hcount] at hle
      rw [← hVfin.cast_ncard_eq]
      have hle' : (P.graphVertices (⋃₀ E)).ncard + 1 - 2 ≤ e := by exact_mod_cast hle
      have hfin : (P.graphVertices (⋃₀ E)).ncard ≤ e + 1 := by omega
      exact_mod_cast hfin
  refine ⟨hvert, ?_⟩
  obtain ⟨hmeet, -⟩ := hM P P.fullRegion Γ hX hΓ hne
  obtain ⟨hin, -, hsixteen, -, -⟩ := hC P P.fullRegion hX
  have hsub : {Q | Q ∈ P.cubes ∧ CubeIntersects Q Γ} ⊆
      ⋃ v ∈ P.graphVertices Γ, P.cubesContaining v := by
    rintro Q ⟨hQ, hm⟩
    obtain ⟨v, hv, hvΓ⟩ := (hmeet Q hQ).1 hm
    exact mem_biUnion hvΓ ⟨hQ, (hin v (isVertex_of_mem_graphVertices P hL hvΓ) Q hQ).2 hv⟩
  calc {Q | Q ∈ P.cubes ∧ CubeIntersects Q Γ}.encard
      ≤ (⋃ v ∈ P.graphVertices Γ, P.cubesContaining v).encard := encard_le_encard hsub
    _ ≤ 16 * (P.graphVertices Γ).encard := by
        refine encard_biUnion_le_sixteen_mul hVfin _ fun v hv => ?_
        have h16 := hsixteen v (isVertex_of_mem_graphVertices P hL hv)
        have hf : (P.cubesContaining v).Finite :=
          finite_of_ncard_ne_zero (by rw [h16]; norm_num)
        rw [← hf.cast_ncard_eq, h16]
        rfl
    _ ≤ 16 * ((e : ℕ∞) + 1) := by gcongr
end YangMills.Construction.PeriodicLattice
end
