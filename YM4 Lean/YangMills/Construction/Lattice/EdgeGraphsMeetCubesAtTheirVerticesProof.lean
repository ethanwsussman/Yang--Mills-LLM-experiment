import YangMills.Construction.Lattice.AdjacentCubesWithThreeCubesInEachDirectionProof
import YangMills.Construction.Lattice.EdgesOfAPartitionAreCompactAndConnected
import YangMills.Construction.Lattice.VerticesAndCubesOfAConnectedEdgeGraphProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.GraphsMeetCubesAtVertices
open CubeLifts
variable (S : LevelUnitPartition)
theorem proj_eq_iff_isPointLift (x : S.Points) (w : Fin 4 → ℝ) :
    S.proj w = x ↔ S.IsPointLift x w := by apply _root_.YangMills.Construction.PeriodicLattice.ThreeWideNeighbours.proj_eq_iff_isPointLift <;> assumption
theorem add_side_smul_coordVec_mem_vertexSet {w : Fin 4 → ℝ} (hw : w ∈ S.vertexSet)
    (ν : Fin 4) : w + (S.side : ℝ) • coordVec ν ∈ S.vertexSet := by apply _root_.YangMills.Construction.PeriodicLattice.EdgeGraphVertexCount.add_side_smul_coordVec_mem_vertexSet <;> assumption
theorem mem_of_mem_graphVertices (hK : LevelUnitPartitionEdgesCompactConnected)
    {Γ : Set S.Points} {v : S.Points} (hv : v ∈ S.graphVertices Γ) : v ∈ Γ := by
  rcases hv with ⟨e, ⟨he, heΓ⟩, hend⟩ | ⟨-, rfl⟩
  · exact heΓ ((hK S e he).2.2 v hend)
  · rfl
theorem exists_edgeEndpoint_mem_cube (hL : CubeLifts.Statement)
    {Δ e : Set S.Points} {x : S.Points} (hΔ : Δ ∈ S.cubes) (he : S.IsEdge e)
    (hxΔ : x ∈ Δ) (hxe : x ∈ e) : ∃ v, S.IsEdgeEndpoint e v ∧ S.IsVertex v ∧ v ∈ Δ := by
  obtain ⟨hT, -, hSites, hV, hP, -⟩ := hL.2.2 S
  obtain ⟨-, -, hpart, -, -, -, hlift, hper, -, -, -⟩ := hT
  obtain ⟨hc, hcube, -, -⟩ := hSites
  obtain ⟨hvert, -, hedge, -, -, -⟩ := hV
  rw [hpart] at hΔ
  obtain ⟨y, rfl⟩ := hΔ
  obtain ⟨w, hw, ν, rfl⟩ := (hedge e).1 he
  obtain ⟨_, ⟨t, ht0, htM, rfl⟩, rfl⟩ := hxe
  obtain ⟨c, hcy⟩ := hlift (y : S.Points)
  rw [hcube y c hcy] at hxΔ
  obtain ⟨z, hz, hzx⟩ := hxΔ
  have hr : IsPeriodVector S (z - (w + t • coordVec ν)) :=
    (hper z _).1 ⟨_, (proj_eq_iff_isPointLift S _ _).1 hzx, (proj_eq_iff_isPointLift S _ _).1 rfl⟩
  obtain ⟨x', h1, h2⟩ := (hper c (c - (z - (w + t • coordVec ν)))).2 (by simpa using hr)
  have hx' : x' = (y : S.Points) :=
    ((proj_eq_iff_isPointLift S _ _).2 h1).symm.trans ((proj_eq_iff_isPointLift S _ _).2 hcy)
  subst hx'
  have hcube' := hcube y _ h2
  have hcentre := (hc _).1 ⟨y, h2⟩
  have hQ : w + t • coordVec ν ∈
      S.closedBox (c - (z - (w + t • coordVec ν))) := by
    intro μ
    have := hz μ
    simp only [Pi.sub_apply, mem_Icc] at this ⊢
    constructor <;> linarith [this.1, this.2]
  rcases (hP _ w ν t hcentre hw ht0 htM hQ).1 with h | h
  · refine ⟨S.proj w, ⟨w, hw, ν, rfl, Or.inl rfl⟩, (hvert _).2 ⟨w, hw, rfl⟩, ?_⟩
    rw [hcube']
    exact ⟨w, h, rfl⟩
  · refine ⟨_, ⟨w, hw, ν, rfl, Or.inr rfl⟩,
      (hvert _).2 ⟨_, add_side_smul_coordVec_mem_vertexSet S hw ν, rfl⟩, ?_⟩
    rw [hcube']
    exact ⟨_, h, rfl⟩
theorem main (hL : CubeLifts.Statement)
    (hG : EdgeGraphsDescribedByCubes)
    (hC : PartitionCubeVertexCornerIncidence)
    (hK : LevelUnitPartitionEdgesCompactConnected) :
    EdgeGraphsMeetCubesAtVertices := by
  intro S X Γ hX hΓ hne
  have hpart : S.cubes = standardCubePartition S.params.L S.params.m S.index :=
    (hL.2.2 S).1.2.2.1
  have hcor := (hC S X hX).1
  have hmeet : ∀ Δ ∈ S.cubes,
      CubeIntersects Δ Γ ↔ ∃ v, S.IsCornerOf v Δ ∧ v ∈ S.graphVertices Γ := by
    intro Δ hΔ
    constructor
    · rintro ⟨x, hxΔ, hxΓ⟩
      rcases (hG S X hX).1.1 Γ hΓ hne with ⟨Δ₀, hΔ₀, v, hv, rfl⟩ | ⟨E, -, -, hE, rfl⟩
      · rw [mem_singleton_iff] at hxΓ
        subst hxΓ
        have hvert : S.IsVertex x := ⟨Δ₀, hpart ▸ hΔ₀.1, hv⟩
        exact ⟨x, (hcor x hvert Δ hΔ).1 hxΔ, Or.inr ⟨hvert, rfl⟩⟩
      · obtain ⟨e, heE, hxe⟩ := hxΓ
        obtain ⟨Δ₁, hΔ₁, heΔ₁⟩ := hE e heE
        have he : S.IsEdge e := ⟨Δ₁, hpart ▸ hΔ₁.1, heΔ₁⟩
        obtain ⟨v, hend, hvert, hvΔ⟩ := exists_edgeEndpoint_mem_cube S hL hΔ he hxΔ hxe
        exact ⟨v, (hcor v hvert Δ hΔ).1 hvΔ, Or.inl ⟨e, ⟨he, subset_sUnion_of_mem heE⟩, hend⟩⟩
    · rintro ⟨v, hv, hvΓ⟩
      exact ⟨v, (hcor v ⟨Δ, hΔ, hv⟩ Δ hΔ).2 hv, mem_of_mem_graphVertices S hK hvΓ⟩
  refine ⟨hmeet, fun Y hY => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hxY, hxΓ⟩
    obtain ⟨C, hC', rfl⟩ := hY
    obtain ⟨Δ, hΔC, hxΔ⟩ := hxY
    have hΔ : Δ ∈ S.cubes := hpart ▸ hC' hΔC
    obtain ⟨v, hv, hvΓ⟩ := (hmeet Δ hΔ).1 ⟨x, hxΔ, hxΓ⟩
    exact ⟨v, hvΓ, Δ, hΔC, (hcor v ⟨Δ, hΔ, hv⟩ Δ hΔ).2 hv⟩
  · rintro ⟨v, hvΓ, hvY⟩
    exact ⟨v, hvY, mem_of_mem_graphVertices S hK hvΓ⟩
end YangMills.Construction.PeriodicLattice.GraphsMeetCubesAtVertices
end
