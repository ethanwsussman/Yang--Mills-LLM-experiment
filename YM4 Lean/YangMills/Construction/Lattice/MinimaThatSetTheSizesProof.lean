import YangMills.Construction.Lattice.ABoxOfTheLevelPartitionIsNotEmpty
import YangMills.Construction.Lattice.EdgeGraphsAndCubes
import YangMills.Construction.Lattice.EdgeGraphsInLargerRegions
import YangMills.Construction.Lattice.EdgeGraphsThatAreNotEmpty
import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdgesProof
import YangMills.Construction.Lattice.MinimaThatSetTheSizes
import YangMills.Construction.Lattice.StandardPartitionCubeGeometry
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.MinimalTreeSizesProof
open CubeLifts EdgeGraphCubeProperties
variable {S : LevelUnitPartition}
theorem isPointLift_iff (x : S.Points) (w : Fin 4 → ℝ) :
    S.IsPointLift x w ↔ S.proj w = x := by apply _root_.YangMills.Construction.PeriodicLattice.CubeLifts.isPointLift_iff <;> assumption
theorem proj_apply (w : Fin 4 → ℝ) (ν : Fin 4) :
    S.proj w ν = ((meshSize S.params.L (levelDepth S.params.K S.level) * w ν : ℝ) :
      AddCircle (torusSide S.params.L S.params.m)) := rfl
theorem proj_add (a b : Fin 4 → ℝ) : S.proj (a + b) = S.proj a + S.proj b := by apply _root_.YangMills.Construction.PeriodicLattice.CubeLifts.proj_add <;> assumption
theorem proj_corner (hT : TorusInCubeUnits S) {p : S.Points} {c : Fin 4 → ℝ}
    (hc : S.IsPointLift p c) (ε : Fin 4 → ℝ) (ν : Fin 4) :
    S.proj (c + ((S.side : ℝ) / 2) • ε) ν =
      p ν + ((ε ν * meshSize S.params.L S.index / 2 : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) := by
  have hW := hT.2.1
  rw [← (isPointLift_iff p c).1 hc, proj_apply, proj_apply, ← AddCircle.coe_add, ← hW]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem side_pos (hT : TorusInCubeUnits S) : (0 : ℝ) < (S.side : ℝ) := by
  exact_mod_cast hT.2.2.2.2.2.2.2.2.2.2
theorem isPeriodVector_sub_of_proj_eq (hT : TorusInCubeUnits S) {a b : Fin 4 → ℝ}
    (h : S.proj a = S.proj b) : IsPeriodVector S (a - b) :=
  (hT.2.2.2.2.2.2.2.1 a b).1 ⟨S.proj a, (isPointLift_iff _ _).2 rfl, (isPointLift_iff _ _).2 h.symm⟩
theorem corner_mem_vertexSet {c : Fin 4 → ℝ} (hc : IsCubeCentre S c) {ε : Fin 4 → ℝ}
    (hε : LevelUnitPartition.IsSigns ε) :
    c + ((S.side : ℝ) / 2) • ε ∈ S.vertexSet := by
  intro μ
  obtain ⟨a, ha⟩ := hc μ
  rcases hε μ with h | h
  · refine ⟨a, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h, ha]
    ring
  · refine ⟨a - 1, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h, ha]
    push_cast
    ring
theorem corner_mem_closedBox (hM : (0 : ℝ) < (S.side : ℝ)) (c : Fin 4 → ℝ) {ε : Fin 4 → ℝ}
    (hε : LevelUnitPartition.IsSigns ε) :
    c + ((S.side : ℝ) / 2) • ε ∈ S.closedBox c := by
  intro μ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc]
  rcases hε μ with h | h <;> rw [h] <;> constructor <;> linarith
theorem isSigns_update {ε : Fin 4 → ℝ} (hε : LevelUnitPartition.IsSigns ε) (ν : Fin 4)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    LevelUnitPartition.IsSigns (Function.update ε ν s) := by
  intro μ
  by_cases h : μ = ν
  · subst h
    simpa using hs
  · rw [Function.update_of_ne h]
    exact hε μ
theorem update_neg_one_update_one {ε : Fin 4 → ℝ} {ν : Fin 4} (h : ε ν = 1) :
    Function.update (Function.update ε ν (-1)) ν 1 = ε := by
  funext μ
  by_cases hμ : μ = ν
  · subst hμ
    simp [h]
  · simp [Function.update_of_ne hμ]
theorem corner_add_side_coordVec (c ε : Fin 4 → ℝ) (ν : Fin 4) (h : ε ν = -1) :
    c + ((S.side : ℝ) / 2) • ε + (S.side : ℝ) • coordVec ν =
      c + ((S.side : ℝ) / 2) • Function.update ε ν 1 := by
  funext μ
  by_cases hμ : μ = ν
  · subst hμ
    simp [coordVec, h]
    ring
  · simp [coordVec, hμ]
structure SettingFacts (S : LevelUnitPartition) (X : Set S.Points) : Prop where
  torus : TorusInCubeUnits S
  sites : SiteAndCubeLifts S
  verts : VertexAndEdgeLifts S
  short : ShortVectorsNotPeriods S
  cover : ∀ C ⊆ standardCubePartition S.params.L S.params.m S.index,
    ∀ Q ∈ standardCubePartition S.params.L S.params.m S.index, Q ⊆ ⋃₀ C → Q ∈ C
  region : IsPartitionRegion S.index X
  cornerIn : ∀ v, S.IsVertex v → ∀ Δ ∈ S.cubes, (v ∈ Δ ↔ S.IsCornerOf v Δ)
  edges : EdgeEndpointFacts S X
  adj : VertexAdjacencyAndConnectivity S
  graphs : S.IsDescribedByCubes X (S.IsEdgeGraphInRegion X)
  whole : S.IsDescribedByCubes S.fullRegion (S.IsEdgeGraphInRegion S.fullRegion)
  larger : ∀ Γ : Set S.Points, S.IsEdgeTreeInRegion X Γ → S.IsGlobalEdgeTree Γ
  length : ∀ Γ : Set S.Points, S.IsGlobalEdgeGraph Γ → Γ.Nonempty →
    (S.graphEdges Γ).Finite ∧
    (S.edgeCount Γ = 0 → ∃ Δ ∈ S.cubes, ∃ v, S.IsCornerOf v Δ ∧ Γ = {v}) ∧
    (1 ≤ S.edgeCount Γ → Γ = ⋃₀ S.graphEdges Γ) ∧
    (1 ≤ S.edgeCount Γ →
      (∃ l, S.EnumeratesEdges (S.graphEdges Γ) l) ∧
        ∀ l, S.EnumeratesEdges (S.graphEdges Γ) l →
          TorusMetric.pathLength (S.edgeSegments l) = (S.side : ℝ) * (S.edgeCount Γ : ℝ)) ∧
    (S.edgeCount Γ = 0 → ∀ x ∈ Γ, (∃ z, S.IsPointLift x z) ∧
      ∀ z, S.IsPointLift x z →
        TorusMetric.pathLength [LevelUnitPartition.degenerateSegment z] =
          (S.side : ℝ) * (S.edgeCount Γ : ℝ)) ∧
    graphLength S.side S.index Γ = S.side * S.edgeCount Γ
  boxes : ∀ B : Set S.Points, IsPartitionBox S.index B → (partitionCubesIn S.index B).Nonempty ∧ B.Nonempty
variable {X : Set S.Points}
theorem isCubeCentre_of_lift (d : SettingFacts S X) {y : Site S.params.L S.params.m S.index}
    {c : Fin 4 → ℝ} (hc : S.IsPointLift (y : S.Points) c) : IsCubeCentre S c :=
  (d.sites.1 c).1 ⟨y, hc⟩
theorem cornerOf_at_lift (d : SettingFacts S X) {y : Site S.params.L S.params.m S.index}
    {c : Fin 4 → ℝ} (hc : S.IsPointLift (y : S.Points) c) {v : S.Points}
    (hv : S.IsCornerOf v (cubeAround y)) :
    ∃ ε, LevelUnitPartition.IsSigns ε ∧
      v = S.proj (c + ((S.side : ℝ) / 2) • ε) := by
  obtain ⟨y', hy, c', hc', ε, hε, rfl⟩ := hv
  have hyy : y = y' := by
    by_contra hne
    exact d.sites.2.2.1 y y' hne hy
  subst hyy
  refine ⟨ε, hε, ?_⟩
  rw [proj_add, proj_add, (isPointLift_iff _ _).1 hc, (isPointLift_iff _ _).1 hc']
theorem exists_cornerOf (d : SettingFacts S X) {Δ : Set S.Points} (hΔ : Δ ∈ S.cubes) :
    ∃ v, S.IsCornerOf v Δ := by
  obtain ⟨y, rfl⟩ := hΔ
  obtain ⟨c, hc⟩ := d.torus.2.2.2.2.2.2.1 (y : S.Points)
  exact ⟨_, y, rfl, c, hc, fun _ => 1, fun _ => Or.inl rfl, rfl⟩
theorem isVertex_of_cornerOf {v : S.Points} {Δ : Set S.Points} (hΔ : Δ ∈ S.cubes)
    (hv : S.IsCornerOf v Δ) : S.IsVertex v := ⟨Δ, hΔ, hv⟩
theorem cornerOf_mem (d : SettingFacts S X) {v : S.Points} {Δ : Set S.Points} (hΔ : Δ ∈ S.cubes)
    (hv : S.IsCornerOf v Δ) : v ∈ Δ :=
  (d.cornerIn v (isVertex_of_cornerOf hΔ hv) Δ hΔ).2 hv
theorem cube_nonempty (d : SettingFacts S X) {Δ : Set S.Points} (hΔ : Δ ∈ S.cubes) : Δ.Nonempty := by
  obtain ⟨v, hv⟩ := exists_cornerOf d hΔ
  exact ⟨v, cornerOf_mem d hΔ hv⟩
theorem cube_isPartitionRegion {Δ : Set S.Points} (hΔ : Δ ∈ S.cubes) : IsPartitionRegion S.index Δ :=
  ⟨{Δ}, singleton_subset_iff.2 hΔ, by simp⟩
theorem edge_of_negative_sign (d : SettingFacts S X) {y : Site S.params.L S.params.m S.index} {c : Fin 4 → ℝ}
    (hc : S.IsPointLift (y : S.Points) c) {ε : Fin 4 → ℝ}
    (hε : LevelUnitPartition.IsSigns ε) {ν : Fin 4} (h : ε ν = -1) :
    S.IsEdgeOf (S.edgeAt (c + ((S.side : ℝ) / 2) • ε) ν) (cubeAround y) ∧
      HasEndpoints S (S.edgeAt (c + ((S.side : ℝ) / 2) • ε) ν)
        (S.proj (c + ((S.side : ℝ) / 2) • ε))
        (S.proj (c + ((S.side : ℝ) / 2) • Function.update ε ν 1)) := by
  have hM := side_pos d.torus
  have hw := corner_mem_vertexSet (isCubeCentre_of_lift d hc) hε
  refine ⟨⟨y, rfl, c, hc, ε, ν, hε, h, rfl⟩, ?_, ⟨_, hw, ν, rfl, Or.inl rfl⟩,
    ⟨_, hw, ν, rfl, Or.inr ?_⟩⟩
  · intro heq
    rw [← corner_add_side_coordVec c ε ν h] at heq
    have hp := isPeriodVector_sub_of_proj_eq d.torus heq
    have hr : ∀ μ, (c + ((S.side : ℝ) / 2) • ε -
        (c + ((S.side : ℝ) / 2) • ε + (S.side : ℝ) • coordVec ν)) μ =
        -((S.side : ℝ) * (coordVec ν μ)) := fun μ => by
      simp
    refine d.short.1 _ ?_ ?_ hp
    · intro h0
      have := congrFun h0 ν
      rw [hr ν] at this
      simp [coordVec] at this
      exact hM.ne' (by exact_mod_cast this)
    · intro μ
      rw [hr μ]
      by_cases hμ : μ = ν
      · subst hμ
        simp [coordVec]
      · simp [coordVec, hμ]
  · rw [corner_add_side_coordVec c ε ν h]
theorem cornerOf_of_endpoint (d : SettingFacts S X) {e Δ : Set S.Points} {v : S.Points}
    (he : S.IsEdgeOf e Δ) (hv : S.IsEdgeEndpoint e v) : S.IsCornerOf v Δ := by
  obtain ⟨y, rfl, c, hc, ε, ν, hε, hν, rfl⟩ := he
  obtain ⟨w, hw, ν', heq, hv⟩ := hv
  obtain ⟨rfl, hp⟩ := d.edges.1 _ (corner_mem_vertexSet (isCubeCentre_of_lift d hc) hε) _ hw _ _ heq
  rcases hv with rfl | rfl
  · exact ⟨y, rfl, c, hc, ε, hε, hp.symm⟩
  · refine ⟨y, rfl, c, hc, Function.update ε ν 1, isSigns_update hε ν (Or.inl rfl), ?_⟩
    rw [proj_add, ← hp, ← proj_add, corner_add_side_coordVec _ _ _ hν]
theorem exists_edge_of_cornerOf (d : SettingFacts S X) {Δ : Set S.Points} {v : S.Points}
    (hv : S.IsCornerOf v Δ) : ∃ e, S.IsEdgeOf e Δ ∧ S.IsEdgeEndpoint e v := by
  obtain ⟨y, rfl, c, hc, ε, hε, rfl⟩ := hv
  rcases hε 0 with h | h
  · have hε' := isSigns_update hε 0 (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
    have := edge_of_negative_sign d hc hε' (ν := 0) (by simp)
    rw [update_neg_one_update_one h] at this
    exact ⟨_, this.1, this.2.2.2⟩
  · have := edge_of_negative_sign d hc hε h
    exact ⟨_, this.1, this.2.2.1⟩
theorem endpoint_mem (d : SettingFacts S X) {e : Set S.Points} {v : S.Points}
    (hv : S.IsEdgeEndpoint e v) : v ∈ e := by
  have hM := side_pos d.torus
  obtain ⟨w, -, ν, rfl, rfl | rfl⟩ := hv
  · exact ⟨w, ⟨0, le_rfl, hM.le, by simp⟩, rfl⟩
  · exact ⟨_, ⟨(S.side : ℝ), hM.le, le_rfl, rfl⟩, rfl⟩
def EdgeStep (W : Set S.Points) (A : Set (Set S.Points)) (a b : S.Points) : Prop :=
  a ∈ W ∧ b ∈ W ∧ ∃ e ∈ A, HasEndpoints S e a b
theorem edgeStep_symm {W : Set S.Points} {A : Set (Set S.Points)} {a b : S.Points}
    (h : EdgeStep W A a b) : EdgeStep W A b a := by
  obtain ⟨ha, hb, e, he, hne, h1, h2⟩ := h
  exact ⟨hb, ha, e, he, hne.symm, h2, h1⟩
abbrev EdgeReach (W : Set S.Points) (A : Set (Set S.Points)) : S.Points → S.Points → Prop :=
  Relation.ReflTransGen (EdgeStep W A)
theorem chainConnected_of_edgeReach {W : Set S.Points} {A : Set (Set S.Points)} {x y : S.Points}
    (hy : y ∈ W) (h : EdgeReach W A x y) : LinkedByChain S W A x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[y], by simpa using hy, List.isChain_singleton _, rfl, rfl⟩
  | @head a b hab _ ih =>
    obtain ⟨l, hW, hch, hh, hl⟩ := ih
    cases l with
    | nil => simp at hh
    | cons b' t =>
      obtain rfl : b' = b := by simpa using hh
      refine ⟨a :: b' :: t, ?_, ?_, rfl, ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hab.1
        · exact hW u hu
      · exact List.isChain_cons_cons.2 ⟨hab.2.2, hch⟩
      · simpa [List.getLast?_cons_cons] using hl
theorem edgeReach_update (d : SettingFacts S X) {W : Set S.Points} {A : Set (Set S.Points)}
    {y : Site S.params.L S.params.m S.index} {c : Fin 4 → ℝ}
    (hc : S.IsPointLift (y : S.Points) c)
    (hW : ∀ v, S.IsCornerOf v (cubeAround y) → v ∈ W) (hA : ∀ e, S.IsEdgeOf e (cubeAround y) → e ∈ A)
    {ε : Fin 4 → ℝ} (hε : LevelUnitPartition.IsSigns ε) (ν : Fin 4) {s : ℝ}
    (hs : s = 1 ∨ s = -1) :
    EdgeReach W A (S.proj (c + ((S.side : ℝ) / 2) • ε))
      (S.proj (c + ((S.side : ℝ) / 2) • Function.update ε ν s)) := by
  have hup : ∀ {ε' : Fin 4 → ℝ}, LevelUnitPartition.IsSigns ε' → ε' ν = -1 →
      EdgeStep W A (S.proj (c + ((S.side : ℝ) / 2) • ε'))
        (S.proj (c + ((S.side : ℝ) / 2) • Function.update ε' ν 1)) := by
    intro ε' hε' h
    have := edge_of_negative_sign d hc hε' h
    exact ⟨hW _ ⟨y, rfl, c, hc, ε', hε', rfl⟩,
      hW _ ⟨y, rfl, c, hc, _, isSigns_update hε' ν (Or.inl rfl), rfl⟩, _, hA _ this.1, this.2⟩
  rcases hε ν with h | h <;> rcases hs with rfl | rfl
  · have : Function.update ε ν 1 = ε := by rw [← h]; exact Function.update_eq_self ν ε
    rw [this]
  · have hε' := isSigns_update hε ν (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
    have := hup hε' (by simp)
    rw [update_neg_one_update_one h] at this
    exact Relation.ReflTransGen.single (edgeStep_symm this)
  · exact Relation.ReflTransGen.single (hup hε h)
  · have : Function.update ε ν (-1) = ε := by rw [← h]; exact Function.update_eq_self ν ε
    rw [this]
theorem edgeReach_within_cube (d : SettingFacts S X) {W : Set S.Points} {A : Set (Set S.Points)}
    {Δ : Set S.Points} (hΔ : Δ ∈ S.cubes)
    (hW : ∀ v, S.IsCornerOf v Δ → v ∈ W) (hA : ∀ e, S.IsEdgeOf e Δ → e ∈ A)
    {v v' : S.Points} (hv : S.IsCornerOf v Δ) (hv' : S.IsCornerOf v' Δ) : EdgeReach W A v v' := by
  obtain ⟨y, rfl⟩ := hΔ
  obtain ⟨c, hc⟩ := d.torus.2.2.2.2.2.2.1 (y : S.Points)
  obtain ⟨ε, hε, rfl⟩ := cornerOf_at_lift d hc hv
  obtain ⟨ε', hε', rfl⟩ := cornerOf_at_lift d hc hv'
  have h1 := isSigns_update hε 0 (hε' 0)
  have h2 := isSigns_update h1 1 (hε' 1)
  have h3 := isSigns_update h2 2 (hε' 2)
  have hlast : Function.update (Function.update (Function.update (Function.update ε 0 (ε' 0))
      1 (ε' 1)) 2 (ε' 2)) 3 (ε' 3) = ε' := by
    funext μ
    fin_cases μ <;> simp [Function.update]
  have := edgeReach_update d hc hW hA h3 3 (hε' 3)
  rw [hlast] at this
  exact ((edgeReach_update d hc hW hA hε 0 (hε' 0)).trans
    (edgeReach_update d hc hW hA h1 1 (hε' 1))).trans
    ((edgeReach_update d hc hW hA h2 2 (hε' 2)).trans this)
theorem exists_common_corner (d : SettingFacts S X) {Q Q' : Set S.Points} (hQ' : Q' ∈ S.cubes)
    (h : HaveCommonFace S.index Q Q') : ∃ u, S.IsCornerOf u Q ∧ S.IsCornerOf u Q' := by
  obtain ⟨F, ⟨y, rfl, μ, ε, hε, rfl⟩, y', hy', μ', ε', -, hF⟩ := h
  obtain ⟨c, hc⟩ := d.torus.2.2.2.2.2.2.1 (y : S.Points)
  have hes : LevelUnitPartition.IsSigns (fun _ => ε) := fun _ => hε
  have hu : S.IsCornerOf (S.proj (c + ((S.side : ℝ) / 2) • fun _ => ε)) (cubeAround y) :=
    ⟨y, rfl, c, hc, _, hes, rfl⟩
  refine ⟨_, hu, ?_⟩
  have hmem : S.proj (c + ((S.side : ℝ) / 2) • fun _ => ε) ∈ cubeAround y := by
    rw [d.sites.2.1 y c hc]
    exact ⟨_, corner_mem_closedBox (side_pos d.torus) c hes, rfl⟩
  have hF' : S.proj (c + ((S.side : ℝ) / 2) • fun _ => ε) ∈
      {x | x ∈ cubeAround y ∧ x μ = (y : FourTorus S.params.L S.params.m) μ +
        ((ε * meshSize S.params.L S.index / 2 : ℝ) :
          AddCircle (torusSide S.params.L S.params.m))} :=
    ⟨hmem, proj_corner d.torus hc _ μ⟩
  rw [hF] at hF'
  exact (d.cornerIn _ (isVertex_of_cornerOf ⟨y, rfl⟩ hu) Q' hQ').1 hF'.1
theorem exists_face_chain (hX : S.IsLevelDomain X) {Q Q' : Set S.Points}
    (hQ : Q ∈ partitionCubesIn S.index X) (hQ' : Q' ∈ partitionCubesIn S.index X) :
    ∃ l : List (Set S.Points), (∀ P ∈ l, P ∈ partitionCubesIn S.index X) ∧
      l.IsChain (HaveCommonFace S.index) ∧ l.head? = some Q ∧ l.getLast? = some Q' := by
  rcases hX with h | h
  · obtain ⟨l, ⟨hl, hch⟩, hh, ht⟩ := h.2.2 Q hQ Q' hQ'
    exact ⟨l, hl, hch.imp (fun _ _ hab => ⟨_, hab.1, hab.2⟩), hh, ht⟩
  · exact h.2 Q hQ Q' hQ'
theorem edgeReach_along_chain (d : SettingFacts S X) {W : Set S.Points} {A : Set (Set S.Points)}
    (hW : ∀ Δ ∈ partitionCubesIn S.index X, ∀ v, S.IsCornerOf v Δ → v ∈ W)
    (hA : ∀ Δ ∈ partitionCubesIn S.index X, ∀ e, S.IsEdgeOf e Δ → e ∈ A) :
    ∀ (l : List (Set S.Points)) (Q Q' : Set S.Points), (∀ P ∈ l, P ∈ partitionCubesIn S.index X) →
      l.IsChain (HaveCommonFace S.index) → l.head? = some Q → l.getLast? = some Q' →
      ∀ v v', S.IsCornerOf v Q → S.IsCornerOf v' Q' → EdgeReach W A v v' := by
  intro l
  induction l with
  | nil =>
    intro Q Q' _ _ h
    simp at h
  | cons a t ih =>
    intro Q Q' hl hch hh ht v v' hv hv'
    obtain rfl : a = Q := by simpa using hh
    have ha : a ∈ partitionCubesIn S.index X := hl a (by simp)
    cases t with
    | nil =>
      obtain rfl : a = Q' := by simpa using ht
      exact edgeReach_within_cube d ha.1 (hW a ha) (hA a ha) hv hv'
    | cons b t' =>
      have hab := List.isChain_cons_cons.1 hch
      have hb : b ∈ partitionCubesIn S.index X := hl b (by simp)
      obtain ⟨u, hu, hu'⟩ := exists_common_corner d hb.1 hab.1
      exact (edgeReach_within_cube d ha.1 (hW a ha) (hA a ha) hv hu).trans
        (ih b Q' (fun P hP => hl P (List.mem_cons_of_mem _ hP)) hab.2 rfl
          (by simpa [List.getLast?_cons_cons] using ht) u v' hu' hv')
def cubeEdges (X : Set S.Points) : Set (Set S.Points) :=
  {e | ∃ Δ ∈ partitionCubesIn S.index X, S.IsEdgeOf e Δ}
theorem cubeEdges_props (d : SettingFacts S X) (hcube : (partitionCubesIn S.index X).Nonempty) :
    (cubeEdges X).Finite ∧ (cubeEdges X).Nonempty ∧
      ∀ a ∈ cubeEdges X, S.IsEdge a := by
  have hpart : ∀ a ∈ cubeEdges X, S.IsEdge a := by
    rintro a ⟨Δ, hΔ, ha⟩
    exact ⟨Δ, hΔ.1, ha⟩
  refine ⟨d.verts.2.2.2.2.1.subset hpart, ?_, hpart⟩
  obtain ⟨Δ, hΔ⟩ := hcube
  obtain ⟨v, hv⟩ := exists_cornerOf d hΔ.1
  obtain ⟨e, he, -⟩ := exists_edge_of_cornerOf d hv
  exact ⟨e, Δ, hΔ, he⟩
theorem cubeEdgeUnion_isTree (d : SettingFacts S X) (hX : S.IsLevelDomain X) (hcube : (partitionCubesIn S.index X).Nonempty) :
    S.IsEdgeTreeInRegion X (S.cubeEdgeUnion X) ∧
      S.graphVertices (S.cubeEdgeUnion X) =
        {v | ∃ Δ ∈ partitionCubesIn S.index X, S.IsCornerOf v Δ} := by
  obtain ⟨hfin, hne, hpart⟩ := cubeEdges_props d hcube
  have hU : S.cubeEdgeUnion X = ⋃₀ cubeEdges X := rfl
  rw [hU]
  have hgraph : S.IsEdgeGraphInRegion X (⋃₀ cubeEdges X) := d.graphs.2.2 _ hne (fun e he => he)
  obtain ⟨hg, hconn⟩ := d.adj.2.2.1 _ hfin hne hpart
  have hEdges : S.graphEdges (⋃₀ cubeEdges X) = cubeEdges X :=
    (d.edges.2.2.2.1 _ _ hg hfin hne hpart rfl).1
  have hV : S.graphVertices (⋃₀ cubeEdges X) =
      {v | ∃ Δ ∈ partitionCubesIn S.index X, S.IsCornerOf v Δ} := by
    ext v
    constructor
    · rintro (⟨e, he, hv⟩ | ⟨hvv, hΓ⟩)
      · rw [hEdges] at he
        obtain ⟨Δ, hΔ, he⟩ := he
        exact ⟨Δ, hΔ, cornerOf_of_endpoint d he hv⟩
      · exfalso
        have h0 := d.edges.2.2.2.2.1 v hvv
        rw [← hΓ, hEdges] at h0
        obtain ⟨e, he⟩ := hne
        rw [h0] at he
        exact he
    · rintro ⟨Δ, hΔ, hv⟩
      obtain ⟨e, he, hve⟩ := exists_edge_of_cornerOf d hv
      exact Or.inl ⟨e, by rw [hEdges]; exact ⟨Δ, hΔ, he⟩, hve⟩
  refine ⟨⟨hgraph, hconn.2 ?_⟩, hV⟩
  intro v hv v' hv'
  apply chainConnected_of_edgeReach hv'
  rw [hV] at hv hv'
  obtain ⟨Q, hQ, hvQ⟩ := hv
  obtain ⟨Q', hQ', hvQ'⟩ := hv'
  obtain ⟨l, hl, hch, hh, ht⟩ := exists_face_chain hX hQ hQ'
  exact edgeReach_along_chain d (fun Δ hΔ u hu => by rw [hV]; exact ⟨Δ, hΔ, hu⟩)
    (fun Δ hΔ e he => by rw [hEdges]; exact ⟨Δ, hΔ, he⟩) l Q Q' hl hch hh ht v v' hvQ hvQ'
theorem cubeEdgeUnion_intersects (d : SettingFacts S X) {R : Set S.Points} (hR : IsPartitionRegion S.index R) (hRX : R ⊆ X)
    (hRne : R.Nonempty) : GraphIntersects (S.cubeEdgeUnion X) R := by
  obtain ⟨C, hC, rfl⟩ := hR
  obtain ⟨x, Q, hQ, hx⟩ := hRne
  have hQX : Q ∈ partitionCubesIn S.index X := ⟨hC hQ, (subset_sUnion_of_mem hQ).trans hRX⟩
  obtain ⟨v, hv⟩ := exists_cornerOf d hQX.1
  obtain ⟨e, he, hve⟩ := exists_edge_of_cornerOf d hv
  exact ⟨v, ⟨e, ⟨Q, hQX, he⟩, endpoint_mem d hve⟩, Q, hQ, cornerOf_mem d hQX.1 hv⟩
theorem nonempty_graphs_finite (d : SettingFacts S X) : {Γ : Set S.Points | S.IsGlobalEdgeGraph Γ ∧ Γ.Nonempty}.Finite := by
  have hfin := (d.verts.2.2.2.1.image (fun v : S.Points => ({v} : Set S.Points))).union
    (d.verts.2.2.2.2.1.finite_subsets.image (fun A : Set (Set S.Points) => ⋃₀ A))
  refine hfin.subset ?_
  rintro Γ ⟨hg, hne⟩
  rcases d.whole.1 Γ hg hne with ⟨Δ, hΔ, v, hv, rfl⟩ | ⟨E, -, -, hE, rfl⟩
  · exact Or.inl ⟨v, isVertex_of_cornerOf hΔ.1 hv, rfl⟩
  · refine Or.inr ⟨E, fun e he => ?_, rfl⟩
    obtain ⟨Δ, hΔ, h⟩ := hE e he
    exact ⟨Δ, hΔ.1, h⟩
theorem tree_isGlobalEdgeGraph (d : SettingFacts S X) {Γ : Set S.Points} (h : S.IsEdgeTreeInRegion X Γ) :
    S.IsGlobalEdgeGraph Γ ∧ Γ.Nonempty :=
  ⟨(d.larger Γ h).1, h.2.nonempty⟩
theorem segmentSumLength_eq (d : SettingFacts S X) {Γ : Set S.Points} (hg : S.IsGlobalEdgeGraph Γ) (hne : Γ.Nonempty)
    {t : ℝ} (h : S.IsSegmentSumLength Γ t) : t = (S.side : ℝ) * (S.edgeCount Γ : ℝ) := by
  obtain ⟨-, -, -, h4, h5, -⟩ := d.length Γ hg hne
  rcases h with ⟨h1, l, hl, rfl⟩ | ⟨h0, x, hx, z, hz, rfl⟩
  · exact (h4 h1).2 l hl
  · exact (h5 h0 x hx).2 z hz
theorem segmentSumLength_holds (d : SettingFacts S X) {Γ : Set S.Points} (hg : S.IsGlobalEdgeGraph Γ)
    (hne : Γ.Nonempty) : S.IsSegmentSumLength Γ ((S.side : ℝ) * (S.edgeCount Γ : ℝ)) := by
  obtain ⟨-, -, -, h4, h5, -⟩ := d.length Γ hg hne
  rcases Nat.eq_zero_or_pos (S.edgeCount Γ) with h0 | h1
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨⟨z, hz⟩, hall⟩ := h5 h0 x hx
    exact Or.inr ⟨h0, x, hx, z, hz, hall z hz⟩
  · obtain ⟨⟨l, hl⟩, hall⟩ := h4 h1
    exact Or.inl ⟨h1, l, hl, hall l hl⟩
theorem isLeast_minTreeEdges {G : Set (Set S.Points)} (hex : ∃ Γ, IsSpanningEdgeTree S.index X G Γ) :
    IsLeast (S.spanningTreeEdgeCounts X G) (S.minTreeEdges X G) := by
  obtain ⟨Γ, h⟩ := hex
  have hne : (S.spanningTreeEdgeCounts X G).Nonempty := ⟨_, Γ, h, rfl⟩
  exact ⟨Nat.sInf_mem hne, fun n hn => Nat.sInf_le hn⟩
theorem minimaExist (d : SettingFacts S X) (hX : S.IsLevelDomain X) (hcube : (partitionCubesIn S.index X).Nonempty)
    {G : Set (Set S.Points)} (hfin : G.Finite)
    (hG : ∀ A ∈ G, IsPartitionRegion S.index A ∧ A ⊆ X ∧ A.Nonempty) : S.MinimaExistFor X G := by
  have hM := side_pos d.torus
  have hM0 : (S.side : ℝ) ≠ 0 := hM.ne'
  have hex : ∃ Γ, IsSpanningEdgeTree S.index X G Γ :=
    ⟨_, (cubeEdgeUnion_isTree d hX hcube).1, fun A hA => cubeEdgeUnion_intersects d (hG A hA).1 (hG A hA).2.1 (hG A hA).2.2⟩
  have hle := isLeast_minTreeEdges hex
  obtain ⟨T, hT, hTe⟩ := hle.1
  obtain ⟨hTg, hTne⟩ := tree_isGlobalEdgeGraph d hT.1
  have hlen : ∀ Γ, IsSpanningEdgeTree S.index X G Γ →
      graphLength S.side S.index Γ = S.side * S.edgeCount Γ := fun Γ h =>
    (d.length Γ (tree_isGlobalEdgeGraph d h.1).1 (tree_isGlobalEdgeGraph d h.1).2).2.2.2.2.2
  have hleast : IsLeast
      {n | ∃ Γ, IsSpanningEdgeTree S.index X G Γ ∧ graphLength S.side S.index Γ = n}
      (S.side * S.minTreeEdges X G) := by
    refine ⟨⟨T, hT, ?_⟩, ?_⟩
    · rw [hlen T hT]
      exact congrArg _ hTe
    · rintro n ⟨Γ, hΓ, rfl⟩
      rw [hlen Γ hΓ]
      exact Nat.mul_le_mul_left _ (hle.2 ⟨Γ, hΓ, rfl⟩)
  have hsInf : minTreeLength S.side S.index X G =
      S.side * S.minTreeEdges X G := hleast.csInf_eq
  refine ⟨(nonempty_graphs_finite d).subset fun Γ h => tree_isGlobalEdgeGraph d h.1, hex,
    ⟨hX, hfin, fun A hA => (hG A hA).1, hex⟩, hle, ?_, ?_, ?_⟩
  · rw [hsInf]
    exact hleast
  · rw [hsInf]
    push_cast
    field_simp
  · refine ⟨(S.side : ℝ) * (S.minTreeEdges X G : ℝ), ⟨⟨T, hT, ?_⟩, ?_⟩, ?_⟩
    · have := segmentSumLength_holds d hTg hTne
      have he : S.edgeCount T = S.minTreeEdges X G := hTe
      rwa [he] at this
    · rintro t ⟨Γ, hΓ, ht⟩
      obtain ⟨hg, hne⟩ := tree_isGlobalEdgeGraph d hΓ.1
      rw [segmentSumLength_eq d hg hne ht]
      have : ((S.minTreeEdges X G : ℕ) : ℝ) ≤ (S.edgeCount Γ : ℝ) := by
        exact_mod_cast hle.2 ⟨Γ, hΓ, rfl⟩
      exact mul_le_mul_of_nonneg_left this hM.le
    · field_simp
theorem cube_target_props (d : SettingFacts S X) {Δ : Set S.Points} (hΔ : Δ ∈ partitionCubesIn S.index X) :
    IsPartitionRegion S.index Δ ∧ Δ ⊆ X ∧ Δ.Nonempty :=
  ⟨cube_isPartitionRegion hΔ.1, hΔ.2, cube_nonempty d hΔ.1⟩
theorem partitionCubesIn_finite (d : SettingFacts S X) : (partitionCubesIn S.index X).Finite :=
  d.sites.2.2.2.subset fun _ h => h.1
theorem minimaExist_cubes (d : SettingFacts S X) (hX : S.IsLevelDomain X)
    (hcube : (partitionCubesIn S.index X).Nonempty) : S.MinimaExistFor X (partitionCubesIn S.index X) :=
  minimaExist d hX hcube (partitionCubesIn_finite d) fun _ h => cube_target_props d h
theorem domainLinearExtent_eq (d : SettingFacts S X) (hX : S.IsLevelDomain X) (hcube : (partitionCubesIn S.index X).Nonempty) :
    S.domainLinearExtent X = (S.minTreeEdges X (partitionCubesIn S.index X) : ℝ) :=
  (minimaExist_cubes d hX hcube).2.2.2.2.2.1
theorem minimaExist_cubesNotIn (d : SettingFacts S X) (hX : S.IsLevelDomain X)
    (hcube : (partitionCubesIn S.index X).Nonempty) (Z : Set S.Points) :
    S.MinimaExistFor X (cubesNotIn S.index X Z) :=
  minimaExist d hX hcube ((partitionCubesIn_finite d).subset fun _ h => h.1) fun _ h => cube_target_props d h.1
theorem sizesAreMinimalEdgeCounts (d : SettingFacts S X) (hX : S.IsLevelDomain X) (hcube : (partitionCubesIn S.index X).Nonempty) :
    S.SizesAreMinimalEdgeCounts X := by
  refine ⟨⟨_, domainLinearExtent_eq d hX hcube, (minimaExist_cubes d hX hcube).2.2.2.1⟩, ?_⟩
  intro Z hZ hout
  have hmin := minimaExist_cubesNotIn d hX hcube Z
  refine ⟨⟨hX, hZ, fun _ => hmin.2.2.1⟩, ?_⟩
  have hrel : S.relativeEdgeSize Z X =
      S.minTreeEdges X (cubesNotIn S.index X Z) := if_pos hout
  rw [hrel]
  exact hmin.2.2.2.1
theorem linearExtentZeroIff (d : SettingFacts S X) (hX : S.IsLevelDomain X) (hcube : (partitionCubesIn S.index X).Nonempty) :
    S.LinearExtentZeroIff X := by
  have hle := (minimaExist_cubes d hX hcube).2.2.2.1
  have hiff : S.domainLinearExtent X = 0 ↔ ∃ v, ∀ Δ ∈ partitionCubesIn S.index X, S.IsCornerOf v Δ := by
    rw [domainLinearExtent_eq d hX hcube]
    constructor
    · intro h0
      have h0' : S.minTreeEdges X (partitionCubesIn S.index X) = 0 := by exact_mod_cast h0
      obtain ⟨Γ, hΓ, hn⟩ := hle.1
      rw [h0'] at hn
      obtain ⟨hg, hne⟩ := tree_isGlobalEdgeGraph d hΓ.1
      obtain ⟨Δ0, hΔ0, v, hv, rfl⟩ := (d.length Γ hg hne).2.1 hn
      refine ⟨v, fun Δ hΔ => ?_⟩
      obtain ⟨x, hx1, hx2⟩ := hΓ.2 Δ hΔ
      rw [mem_singleton_iff] at hx1
      subst hx1
      exact (d.cornerIn _ (isVertex_of_cornerOf hΔ0 hv) Δ hΔ.1).1 hx2
    · rintro ⟨v, hv⟩
      obtain ⟨Δ0, hΔ0⟩ := hcube
      have hgraph : S.IsEdgeGraphInRegion X {v} := d.graphs.2.1 Δ0 hΔ0 v (hv Δ0 hΔ0)
      have htree : IsSpanningEdgeTree S.index X (partitionCubesIn S.index X) {v} :=
        ⟨⟨hgraph, isConnected_singleton⟩, fun Δ hΔ => ⟨v, rfl, cornerOf_mem d hΔ.1 (hv Δ hΔ)⟩⟩
      have h0 : (S.graphEdges {v}).ncard = 0 := by
        rw [d.edges.2.2.2.2.1 v (isVertex_of_cornerOf hΔ0.1 (hv Δ0 hΔ0))]
        simp
      have hz := hle.2 ⟨{v}, htree, h0⟩
      have hz' : S.minTreeEdges X (partitionCubesIn S.index X) = 0 := by omega
      rw [hz']
      simp
  refine ⟨hiff, fun hXp => hiff.2 ?_⟩
  obtain ⟨v, hv⟩ := exists_cornerOf d hXp
  refine ⟨v, fun Δ hΔ => ?_⟩
  have hmem := d.cover {X} (singleton_subset_iff.2 hXp) Δ hΔ.1 (by simpa using hΔ.2)
  rw [mem_singleton_iff] at hmem
  rw [hmem]
  exact hv
theorem islandRegionsAreDomains (I : Set (Set S.Points)) : S.IslandRegionsAreDomains I := by
  refine ⟨fun Y hY => ⟨Or.inl hY.1, hY.2.2⟩, ?_⟩
  intro first Y _ _ h hsub
  rcases h with h | h
  · exact h hsub
  · exact h fun Q hQ => ⟨hQ.1, hQ.2.trans hsub⟩
theorem islandLengthIsMinimalEdgeCount (d : SettingFacts S X) (hX : S.IsLevelDomain X) (hcube : (partitionCubesIn S.index X).Nonempty)
    {I : Set (Set S.Points)} (hI : IsIslandCollection S.index I) :
    S.IslandLengthIsMinimalEdgeCount I X := by
  intro hnot
  have hout : (cubesNotIn S.index X (⋃₀ I)).Nonempty := by
    by_contra hne
    apply hnot
    obtain ⟨C, hC, hXeq⟩ := d.region
    intro x hx
    have hx' := hx
    rw [hXeq] at hx'
    obtain ⟨Q, hQ, hxQ⟩ := hx'
    have hQX : Q ∈ partitionCubesIn S.index X := ⟨hC hQ, hXeq ▸ subset_sUnion_of_mem hQ⟩
    by_contra hxW
    exact hne ⟨Q, hQX, fun h => hxW (h.2 hxQ)⟩
  have htarget : ∀ A ∈ islandTreeTargets S.index I X, IsPartitionRegion S.index A ∧ A ⊆ X ∧ A.Nonempty := by
    rintro A (hA | ⟨hAI, hAX⟩)
    · exact cube_target_props d hA.1
    · exact ⟨(hI.2.1 A hAI).1, hAX, (d.boxes A (hI.2.1 A hAI)).2⟩
  have hfin : (islandTreeTargets S.index I X).Finite :=
    ((partitionCubesIn_finite d).subset fun _ h => h.1).union (hI.1.subset fun _ h => h.1)
  have hmin := minimaExist d hX hcube hfin htarget
  have hle := hmin.2.2.2.1
  have hle0 := (minimaExist_cubes d hX hcube).2.2.2.1
  have hleo := (minimaExist_cubesNotIn d hX hcube (⋃₀ I)).2.2.2.1
  have hrel : S.relativeEdgeSize (⋃₀ I) X =
      S.minTreeEdges X (cubesNotIn S.index X (⋃₀ I)) := if_pos hout
  have hisl : S.islandEdgeLength I X =
      S.minTreeEdges X (islandTreeTargets S.index I X) := rfl
  have hset : S.IslandEdgeLengthDefined I X := ⟨hI, hnot, hmin.2.2.1⟩
  have hlin := domainLinearExtent_eq d hX hcube
  have h1 : S.relativeEdgeSize (⋃₀ I) X ≤ S.islandEdgeLength I X := by
    obtain ⟨T, hT, hTe⟩ := hle.1
    rw [hrel]
    exact hleo.2 ⟨T, ⟨hT.1, fun A hA => hT.2 A (Or.inl hA)⟩, hTe⟩
  have h2 : S.islandEdgeLength I X ≤ S.minTreeEdges X (partitionCubesIn S.index X) := by
    obtain ⟨T, hT, hTe⟩ := hle0.1
    refine hle.2 ⟨T, ⟨hT.1, ?_⟩, hTe⟩
    rintro A (hA | ⟨hAI, hAX⟩)
    · exact hT.2 A hA.1
    · obtain ⟨Q, hQ⟩ := (d.boxes A (hI.2.1 A hAI)).1
      obtain ⟨x, hx1, hx2⟩ := hT.2 Q ⟨hQ.1, hQ.2.trans hAX⟩
      exact ⟨x, hx1, hQ.2 hx2⟩
  refine ⟨hout, hset, hle, ?_, ?_, ?_, ?_⟩
  · obtain ⟨T, hT, hTe⟩ := hle.1
    exact ⟨T, hset, hT, hTe⟩
  · exact_mod_cast h1
  · rw [hlin]
    exact_mod_cast h2
  · intro hno
    have hnoIn : ∀ Q ∈ partitionCubesIn S.index X, Q ∉ partitionCubesIn S.index (⋃₀ I) := by
      intro Q hQ hQW
      have hsub : Q ⊆ ⋃₀ {P | P ∈ standardCubePartition S.params.L S.params.m S.index ∧
          ∃ B ∈ I, P ⊆ B} := by
        intro x hx
        obtain ⟨B, hB, hxB⟩ := hQW.2 hx
        obtain ⟨C, hC, rfl⟩ := (hI.2.1 B hB).1
        obtain ⟨P, hP, hxP⟩ := hxB
        exact ⟨P, ⟨hC hP, _, hB, subset_sUnion_of_mem hP⟩, hxP⟩
      obtain ⟨-, B, hB, hQB⟩ := d.cover _ (fun _ h => h.1) Q hQ.1 hsub
      obtain ⟨x, hx⟩ := cube_nonempty d hQ.1
      exact hno B hB ⟨x, hQ.2 hx, hQB hx⟩
    have hO : cubesNotIn S.index X (⋃₀ I) = partitionCubesIn S.index X :=
      ext fun Q => ⟨fun h => h.1, fun h => ⟨h, hnoIn Q h⟩⟩
    have hTg : islandTreeTargets S.index I X = partitionCubesIn S.index X := by
      ext Q
      constructor
      · rintro (h | ⟨hQI, hQX⟩)
        · exact h.1
        · obtain ⟨x, hx⟩ := (d.boxes Q (hI.2.1 Q hQI)).2
          exact absurd ⟨x, hQX hx, hx⟩ (hno Q hQI)
      · exact fun h => Or.inl ⟨h, hnoIn Q h⟩
    constructor
    · rw [hrel, hisl, hO, hTg]
    · rw [hisl, hTg, hlin]
theorem minimalTreeSizes (hBox : LevelPartitionBoxNonempty)
    (hCubes : StandardPartitionCubeGeometry) (hEdges : EdgeGraphCubeRelations)
    (hLarger : EdgeGraphsExtendToLargerRegions) (hGraphs : EdgeGraphsDescribedByCubes)
    (hLength : EdgeGraphLengthFormula) (hLifts : CubeLifts.Statement) :
    MinimalTreeSizes := by
  intro S X hX hcube
  obtain ⟨-, -, hS⟩ := hLifts
  obtain ⟨hT, -, hsites, hverts, -, hshort⟩ := hS S
  have hreg : IsPartitionRegion S.index X := by
    rcases hX with h | h <;> exact h.1
  obtain ⟨Δ, hΔ⟩ := id hcube
  obtain ⟨y, hy⟩ := hΔ.1
  obtain ⟨c, hc⟩ := hT.2.2.2.2.2.2.1 (y : S.Points)
  have hvΔ : S.IsCornerOf (S.proj (c + ((S.side : ℝ) / 2) • fun _ => 1)) Δ :=
    ⟨y, hy.symm, c, hc, _, fun _ => Or.inl rfl, rfl⟩
  have hG := hGraphs S X hreg
  have hE := hEdges S X _ hreg (hG.1.2.1 Δ hΔ _ hvΔ) (singleton_nonempty _)
  have hwhole : IsPartitionRegion S.index S.fullRegion := ⟨S.cubes, subset_rfl, rfl⟩
  have d : SettingFacts S X :=
    { torus := hT
      sites := hsites
      verts := hverts
      short := hshort
      cover := (hCubes S.params.L S.params.m S.params.isAdmissible.1
        S.params.isAdmissible.2 S.params.m.pos S.index hT.1).2.1.2.2.2.2.2.2
      region := hreg
      cornerIn := hE.2.1.1
      edges := hE.2.2.2.2.2.2.1
      adj := hE.2.2.2.2.2.2.2.1
      graphs := hG.1
      whole := (hGraphs S S.fullRegion hwhole).1
      larger := fun Γ h => ((hLarger S).2 X hreg).2 Γ h
      length := fun Γ hg hne => hLength S Γ hg hne
      boxes := hBox S }
  obtain ⟨ht, hv⟩ := cubeEdgeUnion_isTree d hX hcube
  refine ⟨⟨fun Q hQ Q' hQ' h => exists_common_corner d hQ' ⟨_, h.1, h.2⟩, ht, hv,
    fun R hR hRX hne => cubeEdgeUnion_intersects d hR hRX hne, (nonempty_graphs_finite d)⟩,
    fun G hfin hG' => minimaExist d hX hcube hfin hG', sizesAreMinimalEdgeCounts d hX hcube, linearExtentZeroIff d hX hcube,
    fun I hI => ⟨islandRegionsAreDomains I, islandLengthIsMinimalEdgeCount d hX hcube hI⟩⟩
end YangMills.Construction.PeriodicLattice.MinimalTreeSizesProof
