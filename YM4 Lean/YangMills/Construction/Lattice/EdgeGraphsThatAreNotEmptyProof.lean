import YangMills.Construction.Lattice.MinimaThatSetTheSizesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace EdgeGraphs
open CubeLifts LevelUnitPartition
variable (S : LevelUnitPartition)
theorem isPointLift_iff (x : S.Points) (w : Fin 4 → ℝ) :
    S.IsPointLift x w ↔ S.proj w = x := by apply _root_.YangMills.Construction.PeriodicLattice.CubeLifts.isPointLift_iff <;> assumption
theorem proj_apply (w : Fin 4 → ℝ) (ν : Fin 4) :
    S.proj w ν = ((meshSize S.params.L (levelDepth S.params.K S.level) * w ν : ℝ) :
      AddCircle (torusSide S.params.L S.params.m)) := rfl
theorem proj_congr {w w' : Fin 4 → ℝ} {ν : Fin 4} (h : w ν = w' ν) :
    S.proj w ν = S.proj w' ν := by
  rw [proj_apply, proj_apply, h]
variable {S}
theorem proj_shift_half (hT : TorusInCubeUnits S) {p : S.Points} {c : Fin 4 → ℝ}
    (hc : S.IsPointLift p c) (ε : Fin 4 → ℝ) (ν : Fin 4) :
    S.proj (c + ((S.side : ℝ) / 2) • ε) ν =
      p ν + ((ε ν * meshSize S.params.L S.index / 2 : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) := by apply _root_.YangMills.Construction.PeriodicLattice.MinimalTreeSizesProof.proj_corner <;> assumption
theorem isCubeVertex_iff (hT : TorusInCubeUnits S) (v : S.Points) (Δ : Set S.Points) :
    PeriodicLattice.IsCubeVertex S.index v Δ ↔ S.IsCornerOf v Δ := by
  constructor
  · rintro ⟨y, hΔ, ε, hε, hv⟩
    obtain ⟨c, hc⟩ := hT.2.2.2.2.2.2.1 (y : S.Points)
    exact ⟨y, hΔ, c, hc, ε, hε, funext fun ν => by rw [hv ν, proj_shift_half hT hc]⟩
  · rintro ⟨y, hΔ, c, hc, ε, hε, hv⟩
    exact ⟨y, hΔ, ε, hε, fun ν => by rw [hv, proj_shift_half hT hc]⟩
theorem periodVector_coord_eq_zero (hT : TorusInCubeUnits S) {r : Fin 4 → ℝ}
    (hr : IsPeriodVector S r) (ν : Fin 4) (hb : |r ν| ≤ (S.side : ℝ)) : r ν = 0 := by
  obtain ⟨a, ha⟩ := hr
  have hn : (2 : ℝ) ≤ (S.cubeCount : ℝ) := by exact_mod_cast hT.2.2.2.2.2.2.2.2.2.1
  have hM : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hT.2.2.2.2.2.2.2.2.2.2
  by_cases h0 : a ν = 0
  · rw [ha ν, h0]; simp
  exfalso
  have h1 : (1 : ℝ) ≤ |(a ν : ℝ)| := by
    have : (1 : ℤ) ≤ |a ν| := Int.one_le_abs h0
    exact_mod_cast this
  rw [ha ν, abs_mul, abs_mul, abs_of_pos hM, abs_of_pos (by linarith : (0 : ℝ) < S.cubeCount)]
    at hb
  nlinarith [mul_pos hM (by linarith : (0 : ℝ) < S.cubeCount)]
theorem shift_mem_closedBox (hT : TorusInCubeUnits S) (c : Fin 4 → ℝ) {ε : Fin 4 → ℝ}
    (hε : IsSigns ε) : c + ((S.side : ℝ) / 2) • ε ∈ S.closedBox c := by
  have hM : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hT.2.2.2.2.2.2.2.2.2.2
  intro μ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc]
  rcases hε μ with h | h <;> rw [h] <;> constructor <;> linarith
theorem edge_point_mem_closedBox (hT : TorusInCubeUnits S) (c : Fin 4 → ℝ) {ε : Fin 4 → ℝ}
    (hε : IsSigns ε) {μ : Fin 4} (hμ : ε μ = -1) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ (S.side : ℝ)) :
    c + ((S.side : ℝ) / 2) • ε + t • coordVec μ ∈ S.closedBox c := by
  have hM : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hT.2.2.2.2.2.2.2.2.2.2
  intro ν
  by_cases hν : ν = μ
  · subst hν
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc, coordVec, Pi.single_eq_same,
      hμ]
    constructor <;> linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc, coordVec,
      Pi.single_eq_of_ne hν]
    rcases hε ν with h | h <;> rw [h] <;> constructor <;> linarith
theorem faceLine_eq_edgeAt (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    {y : Site S.params.L S.params.m S.index} {c : Fin 4 → ℝ}
    (hc : S.IsPointLift (y : S.Points) c) {ε : Fin 4 → ℝ} (hε : IsSigns ε) {μ : Fin 4}
    (hμ : ε μ = -1) :
    {x : S.Points | x ∈ cubeAround y ∧ ∀ ν, ν ≠ μ →
      x ν = (y : S.Points) ν + ((ε ν * meshSize S.params.L S.index / 2 : ℝ) :
        AddCircle (torusSide S.params.L S.params.m))} =
      S.edgeAt (c + ((S.side : ℝ) / 2) • ε) μ := by
  have hcube := hC.2.1 y c hc
  have hM : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hT.2.2.2.2.2.2.2.2.2.2
  have hlift := hT.2.2.2.2.2.2.2.1
  ext x
  constructor
  · rintro ⟨hx, hxν⟩
    rw [hcube] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hvcoord : ∀ ν, ν ≠ μ →
        (c + ((S.side : ℝ) / 2) • ε + (u μ - c μ + (S.side : ℝ) / 2) •
          coordVec μ) ν = (c + ((S.side : ℝ) / 2) • ε) ν := by
      intro ν hν
      simp [coordVec, Pi.single_eq_of_ne hν]
    have hvμ : (c + ((S.side : ℝ) / 2) • ε + (u μ - c μ + (S.side : ℝ) / 2) •
        coordVec μ) μ = u μ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordVec, Pi.single_eq_same, hμ]
      ring
    obtain ⟨v, hvdef⟩ : ∃ v, v = c + ((S.side : ℝ) / 2) • ε +
        (u μ - c μ + (S.side : ℝ) / 2) • coordVec μ := ⟨_, rfl⟩
    rw [← hvdef] at hvcoord hvμ
    have hp : S.proj u = S.proj v := by
      funext ν
      by_cases hν : ν = μ
      · subst hν
        exact proj_congr S hvμ.symm
      · rw [hxν ν hν, proj_congr S (hvcoord ν hν), proj_shift_half hT hc]
    have hper : IsPeriodVector S (u - v) :=
      (hlift u v).1 ⟨S.proj u, (isPointLift_iff S _ _).2 rfl, (isPointLift_iff S _ _).2 hp.symm⟩
    have hbμ := hu μ
    rw [mem_Icc] at hbμ
    exact ⟨v, ⟨u μ - c μ + (S.side : ℝ) / 2, by linarith [hbμ.1], by linarith [hbμ.2], hvdef⟩,
      hp.symm⟩
  · rintro ⟨z, ⟨t, h0, h1, rfl⟩, rfl⟩
    refine ⟨?_, fun ν hν => ?_⟩
    · rw [hcube]
      exact ⟨_, edge_point_mem_closedBox hT c hε hμ h0 h1, rfl⟩
    · rw [← proj_shift_half hT hc]
      apply proj_congr
      simp [coordVec, Pi.single_eq_of_ne hν]
theorem isCubeEdge_iff (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (e Δ : Set S.Points) : PeriodicLattice.IsCubeEdge S.index e Δ ↔ S.IsEdgeOf e Δ := by
  constructor
  · rintro ⟨y, rfl, μ, ε, hε, rfl⟩
    obtain ⟨c, hc⟩ := hT.2.2.2.2.2.2.1 (y : S.Points)
    have hε' : IsSigns (Function.update ε μ (-1)) := by
      intro ν
      by_cases hν : ν = μ
      · subst hν; simp
      · rw [Function.update_of_ne hν]; exact hε ν
    refine ⟨y, rfl, c, hc, Function.update ε μ (-1), μ, hε', by simp, ?_⟩
    rw [← faceLine_eq_edgeAt hT hC hc hε' (by simp)]
    ext x
    refine and_congr_right fun _ => forall_congr' fun ν => forall_congr' fun hν => ?_
    rw [Function.update_of_ne hν]
  · rintro ⟨y, rfl, c, hc, ε, ν, hε, hν, rfl⟩
    exact ⟨y, rfl, ν, ε, hε, (faceLine_eq_edgeAt hT hC hc hε hν).symm⟩
theorem mem_of_isCornerOf (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S) {v : S.Points}
    {Δ : Set S.Points} (h : S.IsCornerOf v Δ) : v ∈ Δ := by
  obtain ⟨y, rfl, c, hc, ε, hε, rfl⟩ := h
  rw [hC.2.1 y c hc]
  exact ⟨_, shift_mem_closedBox hT c hε, rfl⟩
theorem subset_of_isEdgeOf (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    {e Δ : Set S.Points} (h : S.IsEdgeOf e Δ) : e ⊆ Δ := by
  obtain ⟨y, rfl, c, hc, ε, ν, hε, hν, rfl⟩ := h
  rw [hC.2.1 y c hc]
  rintro _ ⟨z, ⟨t, h0, h1, rfl⟩, rfl⟩
  exact ⟨_, edge_point_mem_closedBox hT c hε hν h0 h1, rfl⟩
theorem exists_partitionCube_mem {X : Set S.Points} (hX : IsPartitionRegion S.index X)
    {x : S.Points} (hx : x ∈ X) : ∃ Δ ∈ partitionCubesIn S.index X, x ∈ Δ := by
  obtain ⟨C, hC, rfl⟩ := hX
  obtain ⟨Δ, hΔ, hxΔ⟩ := hx
  exact ⟨Δ, ⟨hC hΔ, subset_sUnion_of_mem hΔ⟩, hxΔ⟩
theorem exists_cube_isCornerOf (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (hV : VertexAndEdgeLifts S) {X : Set S.Points} (hX : IsPartitionRegion S.index X)
    {v : S.Points} (hv : S.IsVertex v) (hvX : v ∈ X) :
    ∃ Δ ∈ partitionCubesIn S.index X, S.IsCornerOf v Δ := by
  obtain ⟨Δ, hΔ, hvΔ⟩ := exists_partitionCube_mem hX hvX
  obtain ⟨y, rfl⟩ := hΔ.1
  obtain ⟨c, hc⟩ := hT.2.2.2.2.2.2.1 (y : S.Points)
  rw [hC.2.1 y c hc] at hvΔ
  obtain ⟨u, hu, rfl⟩ := hvΔ
  have huV := hV.2.1 _ u hv ((isPointLift_iff S _ _).2 rfl)
  have hcC : IsCubeCentre S c := (hC.1 c).1 ⟨y, hc⟩
  have hmem : u ∈ S.closedBox c ∩ S.vertexSet := ⟨hu, huV⟩
  rw [hV.2.2.2.2.2 c hcC] at hmem
  obtain ⟨ε, hε, rfl⟩ := hmem
  exact ⟨cubeAround y, hΔ, y, rfl, c, hc, ε, hε, rfl⟩
theorem proj_add_period (hT : TorusInCubeUnits S) (w : Fin 4 → ℝ) {r : Fin 4 → ℝ}
    (hr : IsPeriodVector S r) : S.proj (w + r) = S.proj w := by
  obtain ⟨x, h1, h2⟩ := (hT.2.2.2.2.2.2.2.1 (w + r) w).2 (by simpa using hr)
  rw [(isPointLift_iff S _ _).1 h1, (isPointLift_iff S _ _).1 h2]
theorem edgeAt_add_period (hT : TorusInCubeUnits S) (w : Fin 4 → ℝ) {r : Fin 4 → ℝ}
    (hr : IsPeriodVector S r) (ν : Fin 4) : S.edgeAt (w + r) ν = S.edgeAt w ν := by
  have key : ∀ t : ℝ, S.proj (w + r + t • coordVec ν) =
      S.proj (w + t • coordVec ν) := fun t => by
    rw [add_right_comm]
    exact proj_add_period hT _ hr
  ext x
  constructor
  · rintro ⟨_, ⟨t, h0, h1, rfl⟩, rfl⟩
    exact ⟨_, ⟨t, h0, h1, rfl⟩, (key t).symm⟩
  · rintro ⟨_, ⟨t, h0, h1, rfl⟩, rfl⟩
    exact ⟨_, ⟨t, h0, h1, rfl⟩, key t⟩
theorem exists_cube_isEdgeOf (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (hV : VertexAndEdgeLifts S) (hP : EdgePointsInCube S) {X : Set S.Points}
    (hX : IsPartitionRegion S.index X) {e : Set S.Points} (he : S.IsEdge e) (heX : e ⊆ X) :
    ∃ Δ ∈ partitionCubesIn S.index X, S.IsEdgeOf e Δ := by
  have hM : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hT.2.2.2.2.2.2.2.2.2.2
  obtain ⟨w, hw, ν, rfl⟩ := (hV.2.2.1 e).1 he
  have hmid : S.proj (w + ((S.side : ℝ) / 2) • coordVec ν) ∈ S.edgeAt w ν :=
    ⟨_, ⟨(S.side : ℝ) / 2, by linarith, by linarith, rfl⟩, rfl⟩
  obtain ⟨Δ, hΔ, hmΔ⟩ := exists_partitionCube_mem hX (heX hmid)
  obtain ⟨y, rfl⟩ := hΔ.1
  obtain ⟨c, hc⟩ := hT.2.2.2.2.2.2.1 (y : S.Points)
  have hcube := hC.2.1 y c hc
  rw [hcube] at hmΔ
  obtain ⟨u, hu, huE⟩ := hmΔ
  have hper : IsPeriodVector S (u - (w + ((S.side : ℝ) / 2) • coordVec ν)) :=
    (hT.2.2.2.2.2.2.2.1 _ _).1 ⟨S.proj u, (isPointLift_iff S _ _).2 rfl,
      (isPointLift_iff S _ _).2 huE.symm⟩
  obtain ⟨r, hr⟩ : ∃ r, r = u - (w + ((S.side : ℝ) / 2) • coordVec ν) := ⟨_, rfl⟩
  rw [← hr] at hper
  have hvertex : S.IsVertex (S.proj w) := (hV.1 _).2 ⟨w, hw, rfl⟩
  have hw' : w + r ∈ S.vertexSet :=
    hV.2.1 _ _ hvertex ((isPointLift_iff S _ _).2 (proj_add_period hT w hper))
  have hu' : w + r + ((S.side : ℝ) / 2) • coordVec ν = u := by
    rw [hr]; abel
  have hcC : IsCubeCentre S c := (hC.1 c).1 ⟨y, hc⟩
  have hedge := (hP c (w + r) ν ((S.side : ℝ) / 2) hcC hw' (by linarith) (by linarith)
    (by rw [hu']; exact hu)).2 (by linarith) (by linarith)
  rw [← hcube, edgeAt_add_period hT w hper] at hedge
  exact ⟨cubeAround y, hΔ, hedge.2⟩
theorem edges_finite (hV : VertexAndEdgeLifts S) {X : Set S.Points}
    {E : Set (Set S.Points)} (hE : ∀ e ∈ E, ∃ Δ ∈ partitionCubesIn S.index X, S.IsEdgeOf e Δ) :
    E.Finite :=
  hV.2.2.2.2.1.subset fun e he => by
    obtain ⟨Δ, hΔ, hΔe⟩ := hE e he
    exact ⟨Δ, hΔ.1, hΔe⟩
theorem nonempty_of_sUnion_nonempty {E : Set (Set S.Points)} (h : (⋃₀ E).Nonempty) :
    E.Nonempty := by
  obtain ⟨_, e, he, _⟩ := h
  exact ⟨e, he⟩
end EdgeGraphs
open EdgeGraphs in
theorem edgeGraphsDescribedByCubes_holds (h : CubeLifts.Statement) :
    EdgeGraphsDescribedByCubes := by
  intro S X hX
  obtain ⟨hT, -, hC, hV, hP, -⟩ := h.2.2 S
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro Γ hΓ hne
    rcases hΓ with ⟨Q, hQ, c, hc, rfl⟩ | ⟨E, hE, rfl⟩
    · exact Or.inl ⟨Q, hQ, c, (isCubeVertex_iff hT _ _).1 hc, rfl⟩
    · have hE' : ∀ e ∈ E, ∃ Δ ∈ partitionCubesIn S.index X, S.IsEdgeOf e Δ := fun e he => by
        obtain ⟨Q, hQ, hQe⟩ := hE e he
        exact ⟨Q, hQ, (isCubeEdge_iff hT hC _ _).1 hQe⟩
      exact Or.inr ⟨E, edges_finite hV hE', nonempty_of_sUnion_nonempty hne, hE', rfl⟩
  · intro Δ hΔ v hv
    exact Or.inl ⟨Δ, hΔ, v, (isCubeVertex_iff hT _ _).2 hv, rfl⟩
  · intro E _ hE
    refine Or.inr ⟨E, fun e he => ?_, rfl⟩
    obtain ⟨Δ, hΔ, hΔe⟩ := hE e he
    exact ⟨Δ, hΔ, (isCubeEdge_iff hT hC _ _).2 hΔe⟩
  · intro Γ hΓ hne
    rcases hΓ with ⟨Q, hQ, c, hc, hcX, rfl⟩ | ⟨E, hE, rfl⟩
    · obtain ⟨Δ, hΔ, hcΔ⟩ :=
        exists_cube_isCornerOf hT hC hV hX ⟨Q, hQ, (isCubeVertex_iff hT _ _).1 hc⟩ hcX
      exact Or.inl ⟨Δ, hΔ, c, hcΔ, rfl⟩
    · have hE' : ∀ e ∈ E, ∃ Δ ∈ partitionCubesIn S.index X, S.IsEdgeOf e Δ := fun e he => by
        obtain ⟨heX, Q, hQ, hQe⟩ := hE e he
        exact exists_cube_isEdgeOf hT hC hV hP hX ⟨Q, hQ, (isCubeEdge_iff hT hC _ _).1 hQe⟩ heX
      exact Or.inr ⟨E, edges_finite hV hE', nonempty_of_sUnion_nonempty hne, hE', rfl⟩
  · intro Δ hΔ v hv
    exact Or.inl ⟨Δ, hΔ.1, v, (isCubeVertex_iff hT _ _).2 hv, hΔ.2 (mem_of_isCornerOf hT hC hv),
      rfl⟩
  · intro E _ hE
    refine Or.inr ⟨E, fun e he => ?_, rfl⟩
    obtain ⟨Δ, hΔ, hΔe⟩ := hE e he
    exact ⟨(subset_of_isEdgeOf hT hC hΔe).trans hΔ.2, Δ, hΔ.1, (isCubeEdge_iff hT hC _ _).2 hΔe⟩
end YangMills.Construction.PeriodicLattice
