import YangMills.Construction.Lattice.AdjacentVerticesAndConnectedEdgeGraphs
import YangMills.Construction.Lattice.EdgeGraphsInLargerRegions
import YangMills.Construction.Lattice.EdgeGraphsMeetCubesAtTheirVertices
import YangMills.Construction.Lattice.EdgeGraphsThatAreNotEmpty
import YangMills.Construction.Lattice.EdgesOfAPartitionAndTheirEndPoints
import YangMills.Construction.Lattice.EdgesOfAPartitionAreCompactAndConnected
import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdges
import YangMills.Construction.Lattice.NumberingOfVerticesAlongEdges
import YangMills.Construction.Lattice.VerticesAndCubesOfAConnectedEdgeGraph
import YangMills.Construction.Lattice.VerticesOfAShortestEdgeTree
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open EdgeGraphCubeProperties CubeLifts LevelUnitPartition in
theorem shortestEdgeTreeVertexBound_of_lattice_facts
    (hLift : CubeLifts.Statement)
    (hDesc : EdgeGraphsDescribedByCubes)
    (hExt : EdgeGraphsExtendToLargerRegions)
    (hEnds : PartitionEdgeEndpoints)
    (hMeet : EdgeGraphsMeetCubesAtVertices)
    (hAdj : AdjacentVerticesConnectEdgeGraphs)
    (hNum : VerticesNumberedAlongEdges)
    (hCount : ConnectedEdgeGraphVerticesAndCubes)
    (hCpt : LevelUnitPartitionEdgesCompactConnected) :
    ShortestEdgeTreeVertexBound := by
  intro S X Γ hX hΓ hne G _ hGr hTree hMin
  obtain ⟨hT, -, -, hV, -, -⟩ := hLift.2.2 S
  have hpart : S.cubes = standardCubePartition S.params.L S.params.m S.index := hT.2.2.1
  have hM : 0 < S.side := hT.2.2.2.2.2.2.2.2.2.2
  have hW : IsPartitionRegion S.index S.fullRegion := ⟨S.cubes, hpart.subset, rfl⟩
  obtain ⟨-, hTwo, -, hUnion, hCorner, -⟩ := hEnds S S.fullRegion hW
  obtain ⟨-, -, hJoin, hTreeVerts⟩ := hAdj S
  have hGraph : S.IsGlobalEdgeGraph Γ := ((hExt S).2 X hX).1 Γ hne hΓ
  have hTreeW : S.IsGlobalEdgeTree Γ := ((hExt S).2 X hX).2 Γ hTree.1
  have hconn : IsConnected Γ := hTree.1.2
  obtain ⟨hVert, hWne, -⟩ := hTreeVerts Γ hTreeW
  have hfinE : (S.graphEdges Γ).Finite := hV.2.2.2.2.1.subset fun e h => h.1
  have hfinV : (S.graphVertices Γ).Finite := hV.2.2.2.1.subset fun v h => hVert v h
  have hle : (S.graphVertices Γ).encard ≤ (S.graphEdges Γ).encard + 1 := by
    have h := (hCount S (S.graphEdges Γ).ncard Γ hGraph hconn hfinE.cast_ncard_eq.symm).1
    rwa [hfinE.cast_ncard_eq] at h
  rcases (hDesc S X hX).1.1 Γ hΓ hne with ⟨Δ, hΔ, v, hv, rfl⟩ | ⟨E, hEf, hEn, hEe, rfl⟩
  · have hΔp : Δ ∈ S.cubes := by
      rw [hpart]
      exact hΔ.1
    have hvV : S.IsVertex v := ⟨Δ, hΔp, hv⟩
    have h0 := hCorner v hvV
    have hverts : S.graphVertices {v} = {v} := by
      ext u
      constructor
      · rintro (⟨e, he, -⟩ | ⟨-, h⟩)
        · rw [h0] at he
          exact he.elim
        · exact (singleton_eq_singleton_iff.1 h).symm
      · rintro rfl
        exact Or.inr ⟨hvV, rfl⟩
    rw [hverts, h0]
    simp
  · have hEp : ∀ e ∈ E, S.IsEdge e := fun e he => by
      obtain ⟨Δ, hΔ, h⟩ := hEe e he
      refine ⟨Δ, ?_, h⟩
      rw [hpart]
      exact hΔ.1
    obtain ⟨hedges, hcard⟩ := hUnion (⋃₀ E) E hGraph hEf hEn hEp rfl
    rw [hedges] at hle ⊢
    refine le_antisymm hle ?_
    by_contra hlt
    have hq : (S.graphVertices (⋃₀ E)).ncard ≤ E.ncard := by
      rw [← hEf.cast_ncard_eq, ← hfinV.cast_ncard_eq] at hlt
      have h : ¬ (E.ncard + 1 ≤ (S.graphVertices (⋃₀ E)).ncard) := fun h =>
        hlt (by exact_mod_cast h)
      omega
    obtain ⟨B0, hB0⟩ := hEn
    have hjoined := (hJoin E hEf ⟨B0, hB0⟩ hEp).2.1 hconn
    rw [hedges] at hjoined
    have hends : ∀ a ∈ E, ∀ v, S.IsEdgeEndpoint a v → v ∈ S.graphVertices (⋃₀ E) :=
      fun a ha v hv => Or.inl ⟨a, hedges.symm ▸ ha, hv⟩
    have h2 : 2 ≤ (S.graphVertices (⋃₀ E)).ncard := by
      have h := ncard_le_ncard (s := {v | S.IsEdgeEndpoint B0 v}) (hends B0 hB0) hfinV
      rwa [hTwo B0 (hEp B0 hB0)] at h
    obtain ⟨F, hFW⟩ := hWne
    obtain ⟨v, -, -, a, ha, hinj, hlast⟩ := hNum S (S.graphVertices (⋃₀ E)) _ E hfinV rfl
      (by omega) hVert (fun e he => ⟨hEp e he, hends e he⟩) hjoined F hFW
    obtain ⟨hTconn, hWT⟩ := hlast h2
    have himg : (a '' Icc 2 (S.graphVertices (⋃₀ E)).ncard).ncard < E.ncard := by
      rw [hinj.ncard_image]
      have h : (Icc 2 (S.graphVertices (⋃₀ E)).ncard : Set ℕ).ncard =
          (S.graphVertices (⋃₀ E)).ncard + 1 - 2 := by
        rw [← Finset.coe_Icc, ncard_coe_finset, Nat.card_Icc]
      omega
    obtain ⟨B, hBE, hBa⟩ := exists_mem_notMem_of_ncard_lt_ncard himg ((finite_Icc _ _).image a)
    have ha' : ∀ k ∈ Icc 2 (S.graphVertices (⋃₀ E)).ncard, a k ∈ E \ {B} :=
      fun k hk => ⟨(ha k hk.1 hk.2).1, fun h => hBa ⟨k, hk, h⟩⟩
    have hRf : (E \ {B}).Finite := hEf.subset sdiff_subset
    have hRn : (E \ {B}).Nonempty := ⟨a 2, ha' 2 ⟨le_rfl, h2⟩⟩
    have hRp : ∀ e ∈ E \ {B}, S.IsEdge e := fun e he => hEp e he.1
    have hGraph' : S.IsGlobalEdgeGraph (⋃₀ (E \ {B})) := (hJoin _ hRf hRn hRp).1
    obtain ⟨-, hcard'⟩ := hUnion _ _ hGraph' hRf hRn hRp rfl
    have hTA : (⋃ k ∈ Icc 2 (S.graphVertices (⋃₀ E)).ncard, a k) ⊆ ⋃₀ (E \ {B}) :=
      iUnion₂_subset fun k hk => subset_sUnion_of_mem (ha' k hk)
    have hconn' : IsConnected (⋃₀ (E \ {B})) := by
      obtain ⟨x, hx⟩ := hTconn.nonempty
      have hunion : ⋃₀ (E \ {B}) =
          ⋃₀ ((fun e => (⋃ k ∈ Icc 2 (S.graphVertices (⋃₀ E)).ncard, a k) ∪ e) '' (E \ {B})) := by
        apply Subset.antisymm
        · rintro y ⟨e, he, hy⟩
          exact ⟨_, ⟨e, he, rfl⟩, Or.inr hy⟩
        · rintro y ⟨_, ⟨e, he, rfl⟩, hy | hy⟩
          · exact hTA hy
          · exact ⟨e, he, hy⟩
      refine ⟨⟨x, hTA hx⟩, ?_⟩
      rw [hunion]
      refine isPreconnected_sUnion x _ ?_ ?_
      · rintro _ ⟨e, -, rfl⟩
        exact Or.inl hx
      · rintro _ ⟨e, he, rfl⟩
        have hep := hEp e he.1
        obtain ⟨-, hec, hes⟩ := hCpt S e hep
        have hne' : {v | S.IsEdgeEndpoint e v}.Nonempty := by
          apply nonempty_of_ncard_ne_zero
          rw [hTwo e hep]
          norm_num
        obtain ⟨u, hu⟩ := hne'
        exact IsPreconnected.union u (hWT (hends e he.1 u hu)) (hes u hu)
          hTconn.isPreconnected hec.isPreconnected
    have hGraphX : S.IsEdgeGraphInRegion X (⋃₀ (E \ {B})) :=
      (hDesc S X hX).1.2.2 _ hRn fun e he => hEe e he.1
    have hTree' : IsSpanningEdgeTree S.index X G (⋃₀ (E \ {B})) := by
      refine ⟨⟨hGraphX, hconn'⟩, fun Y hY => ?_⟩
      have hmeet : (Y ∩ ⋃₀ E).Nonempty := by
        rw [inter_comm]
        exact hTree.2 Y hY
      obtain ⟨u, hu, huY⟩ := ((hMeet S X (⋃₀ E) hX hΓ hne).2 Y (hGr Y hY)).1 hmeet
      exact ⟨u, hTA (hWT hu), huY⟩
    have hlen := hMin _ hTree'
    rw [graphLength_le_graphLength_iff hM, hcard, hcard'] at hlen
    have hlt' := ncard_sdiff_singleton_lt_of_mem hBE hEf
    omega
end YangMills.Construction.PeriodicLattice
end
