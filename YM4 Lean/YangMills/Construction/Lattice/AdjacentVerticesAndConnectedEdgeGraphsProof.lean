import YangMills.Construction.Lattice.AdjacentVerticesAndConnectedEdgeGraphs
import YangMills.Construction.Lattice.EdgeGraphsThatAreNotEmpty
import YangMills.Construction.Lattice.EdgesOfAPartitionAndTheirEndPoints
import YangMills.Construction.Lattice.EdgesOfAPartitionAreCompactAndConnected
import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdges
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.AdjacencyAndConnectedGraphs
open EdgeGraphCubeProperties CubeLifts
variable {S : LevelUnitPartition}
theorem isPointLift_proj (w : Fin 4 → ℝ) : S.IsPointLift (S.proj w) w :=
  (levelProj_eq_iff_isLevelLift (by have := S.params.isAdmissible.2; omega) _ _ _ _
    _).mp rfl
theorem proj_eq_iff (T : TorusInCubeUnits S) (w w' : Fin 4 → ℝ) :
    S.proj w = S.proj w' ↔ IsPeriodVector S (w - w') := by
  obtain ⟨-, -, -, -, -, -, -, hPer, -⟩ := T
  constructor
  · intro h
    exact (hPer w w').mp ⟨S.proj w, isPointLift_proj w, h ▸ isPointLift_proj w'⟩
  · intro h
    obtain ⟨x, h1, h2⟩ := (hPer w w').mpr h
    have hL : S.params.L ≠ 0 := by have := S.params.isAdmissible.2; omega
    exact ((levelProj_eq_iff_isLevelLift hL _ _ _ _ _).mpr h1).trans
      ((levelProj_eq_iff_isLevelLift hL _ _ _ _ _).mpr h2).symm
theorem proj_add_congr (T : TorusInCubeUnits S) {w w' : Fin 4 → ℝ}
    (h : S.proj w = S.proj w') (u : Fin 4 → ℝ) :
    S.proj (w + u) = S.proj (w' + u) := by
  rw [proj_eq_iff T] at h ⊢
  have : w + u - (w' + u) = w - w' := by abel
  rwa [this]
theorem signedStep_one (ν : Fin 4) :
    EdgeGraphCubeProperties.signedStep S ν 1 = (S.side : ℝ) • coordVec ν := by
  simp [EdgeGraphCubeProperties.signedStep]
theorem add_side_add_signedStep_neg_one (w : Fin 4 → ℝ) (ν : Fin 4) :
    w + (S.side : ℝ) • coordVec ν + EdgeGraphCubeProperties.signedStep S ν (-1) = w := by
  simp [EdgeGraphCubeProperties.signedStep]
theorem add_signedStep_neg_one_add_side (w : Fin 4 → ℝ) (ν : Fin 4) :
    w + EdgeGraphCubeProperties.signedStep S ν (-1) + (S.side : ℝ) • coordVec ν = w := by
  simp [EdgeGraphCubeProperties.signedStep]
theorem add_signedStep_mem {w : Fin 4 → ℝ} (hw : w ∈ S.vertexSet) (ν : Fin 4) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : w + EdgeGraphCubeProperties.signedStep S ν σ ∈ S.vertexSet := by
  intro μ
  obtain ⟨a, ha⟩ := hw μ
  by_cases h : μ = ν
  · subst h
    rcases hσ with rfl | rfl
    · refine ⟨a + 1, ?_⟩
      simp [EdgeGraphCubeProperties.signedStep, coordVec, ha]
      ring
    · refine ⟨a - 1, ?_⟩
      simp [EdgeGraphCubeProperties.signedStep, coordVec, ha]
      ring
  · refine ⟨a, ?_⟩
    simp [EdgeGraphCubeProperties.signedStep, coordVec, ha, h]
theorem proj_ne_proj_add_signedStep (hM : 0 < S.side) (T : TorusInCubeUnits S)
    (hS : ShortVectorsNotPeriods S) (w : Fin 4 → ℝ) (ν : Fin 4) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : S.proj w ≠ S.proj (w + EdgeGraphCubeProperties.signedStep S ν σ) := by
  intro h
  have hper := (proj_eq_iff T _ _).1 h
  have hM' : (S.side : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine hS.1 _ ?_ ?_ hper
  · intro h0
    have := congrFun h0 ν
    rcases hσ with rfl | rfl <;> simp [EdgeGraphCubeProperties.signedStep, coordVec, hM'] at this
  · intro μ
    by_cases hμ : μ = ν
    · subst hμ
      rcases hσ with rfl | rfl <;> simp [EdgeGraphCubeProperties.signedStep, coordVec]
    · simp [EdgeGraphCubeProperties.signedStep, coordVec, hμ]
theorem adjacent_proj_iff (hM : 0 < S.side) (T : TorusInCubeUnits S)
    (hV : VertexAndEdgeLifts S) (hS : ShortVectorsNotPeriods S)
    (hdet : ∀ w ∈ S.vertexSet, ∀ w' ∈ S.vertexSet, ∀ ν ν' : Fin 4,
      S.edgeAt w ν = S.edgeAt w' ν' → ν = ν' ∧ S.proj w = S.proj w')
    {w : Fin 4 → ℝ} (hw : w ∈ S.vertexSet) (v : S.Points) :
    S.Adjacent (S.proj w) v ↔
      ∃ (ν : Fin 4) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧
        v = S.proj (w + EdgeGraphCubeProperties.signedStep S ν σ) := by
  obtain ⟨hvert, -, hedge, -, -, -⟩ := hV
  constructor
  · rintro ⟨-, -, hne, e, -, ⟨w₁, hw₁, ν₁, he₁, h₁⟩, ⟨w₂, hw₂, ν₂, he₂, h₂⟩⟩
    obtain ⟨rfl, hc⟩ := hdet w₁ hw₁ w₂ hw₂ ν₁ ν₂ (he₁.symm.trans he₂)
    have hc' := proj_add_congr T hc ((S.side : ℝ) • coordVec ν₁)
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact absurd (h₁.trans (hc.trans h₂.symm)) hne
    · refine ⟨ν₁, 1, Or.inl rfl, ?_⟩
      rw [h₂, ← hc', signedStep_one]
      exact proj_add_congr T h₁.symm _
    · refine ⟨ν₁, -1, Or.inr rfl, ?_⟩
      rw [proj_add_congr T h₁ (EdgeGraphCubeProperties.signedStep S ν₁ (-1)),
        add_side_add_signedStep_neg_one, h₂, hc]
    · exact absurd (h₁.trans (hc'.trans h₂.symm)) hne
  · rintro ⟨ν, σ, hσ, rfl⟩
    have hw' := add_signedStep_mem hw ν hσ
    refine ⟨(hvert _).2 ⟨w, hw, rfl⟩, (hvert _).2 ⟨_, hw', rfl⟩,
      proj_ne_proj_add_signedStep hM T hS w ν hσ, ?_⟩
    rcases hσ with rfl | rfl
    · refine ⟨S.edgeAt w ν, (hedge _).2 ⟨w, hw, ν, rfl⟩, ⟨w, hw, ν, rfl, Or.inl rfl⟩,
        ⟨w, hw, ν, rfl, Or.inr (by rw [signedStep_one])⟩⟩
    · refine ⟨S.edgeAt (w + EdgeGraphCubeProperties.signedStep S ν (-1)) ν, (hedge _).2 ⟨_, hw', ν, rfl⟩,
        ⟨_, hw', ν, rfl, Or.inr (by rw [add_signedStep_neg_one_add_side])⟩, ⟨_, hw', ν, rfl, Or.inl rfl⟩⟩
theorem encard_adjacent_le_eight (w : Fin 4 → ℝ)
    (h : ∀ v, S.Adjacent (S.proj w) v →
      ∃ (ν : Fin 4) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧
        v = S.proj (w + EdgeGraphCubeProperties.signedStep S ν σ)) :
    {v' | S.Adjacent (S.proj w) v'}.encard ≤ 8 := by
  have hsub : {v' | S.Adjacent (S.proj w) v'} ⊆
      (fun p : Fin 4 × Bool =>
        S.proj (w + EdgeGraphCubeProperties.signedStep S p.1 (if p.2 then 1 else -1))) '' univ := by
    intro v hv
    obtain ⟨ν, σ, hσ, rfl⟩ := h v hv
    rcases hσ with rfl | rfl
    · exact ⟨(ν, true), mem_univ _, by simp⟩
    · exact ⟨(ν, false), mem_univ _, by simp⟩
  have hcard : (univ : Set (Fin 4 × Bool)).encard = 8 := by
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    simp
  calc _ ≤ _ := Set.encard_le_encard hsub
    _ ≤ _ := Set.encard_image_le _ _
    _ = 8 := hcard
theorem chainConnected_refl {W : Set S.Points} {A : Set (Set S.Points)} {x : S.Points} (hx : x ∈ W) :
    LinkedByChain S W A x x :=
  ⟨[x], by simpa using hx, List.isChain_singleton _, rfl, rfl⟩
theorem chainConnected_snoc {W : Set S.Points} {A : Set (Set S.Points)} {x a b : S.Points}
    (h : LinkedByChain S W A x a) (hb : b ∈ W) (hab : ∃ e ∈ A, HasEndpoints S e a b) :
    LinkedByChain S W A x b := by
  obtain ⟨c, hW, hc, hh, hl⟩ := h
  refine ⟨c ++ [b], ?_, ?_, ?_, ?_⟩
  · intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact hW u hu
    · rw [List.mem_singleton.1 hu]
      exact hb
  · refine List.IsChain.append hc (List.isChain_singleton _) ?_
    intro p hp q hq
    rw [hl] at hp
    simp only [Option.mem_def, Option.some.injEq] at hp
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
    subst hp
    subst hq
    exact hab
  · simp [List.head?_append, hh]
  · simp
theorem chainConnected_of_isPreconnected (hK : LevelUnitPartitionEdgesCompactConnected)
    {A : Set (Set S.Points)} (hfin : A.Finite) (hedge : ∀ a ∈ A, S.IsEdge a)
    (hmid : ∀ e e', S.IsEdge e → S.IsEdge e' → e ≠ e' →
      ∀ x, x ∈ e → x ∈ e' → S.IsEdgeEndpoint e x ∧ S.IsEdgeEndpoint e' x)
    (hcon : IsPreconnected (⋃₀ A)) {W : Set S.Points}
    (hW : ∀ v, v ∈ W ↔ ∃ e ∈ A, S.IsEdgeEndpoint e v) {v₀ : S.Points} (hv₀ : v₀ ∈ W) :
    ∀ v ∈ W, LinkedByChain S W A v₀ v := by
  classical
  have hstep : ∀ e ∈ A, ∀ a b, S.IsEdgeEndpoint e a → S.IsEdgeEndpoint e b →
      LinkedByChain S W A v₀ a → LinkedByChain S W A v₀ b := by
    intro e he a b ha hb hj
    by_cases hab : a = b
    · exact hab ▸ hj
    · exact chainConnected_snoc hj ((hW b).2 ⟨e, he, hb⟩) ⟨e, he, hab, ha, hb⟩
  have hclosed : ∀ B : Set (Set S.Points), B ⊆ A → IsClosed (⋃₀ B) := by
    intro B hB
    rw [sUnion_eq_biUnion]
    exact (hfin.subset hB).isClosed_biUnion fun e he => (hK S e (hedge e (hB he))).1.isClosed
  set A₁ : Set (Set S.Points) := {e | e ∈ A ∧ ∃ a, S.IsEdgeEndpoint e a ∧ LinkedByChain S W A v₀ a}
    with hA₁
  set A₂ : Set (Set S.Points) := {e | e ∈ A ∧ ¬∃ a, S.IsEdgeEndpoint e a ∧ LinkedByChain S W A v₀ a}
    with hA₂
  have hempty : ∀ e, e ∉ A₂ := by
    intro e₂ he₂
    obtain ⟨e₀, he₀, hend₀⟩ := (hW v₀).1 hv₀
    have h₀ : e₀ ∈ A₁ := ⟨he₀, v₀, hend₀, chainConnected_refl hv₀⟩
    have hne₁ : (⋃₀ A ∩ ⋃₀ A₁).Nonempty := by
      have hm := (hK S e₀ (hedge e₀ he₀)).2.2 v₀ hend₀
      exact ⟨v₀, ⟨e₀, he₀, hm⟩, ⟨e₀, h₀, hm⟩⟩
    have hne₂ : (⋃₀ A ∩ ⋃₀ A₂).Nonempty := by
      obtain ⟨x, hx⟩ := (hK S e₂ (hedge e₂ he₂.1)).2.1.nonempty
      exact ⟨x, ⟨e₂, he₂.1, hx⟩, ⟨e₂, he₂, hx⟩⟩
    have hcover : ⋃₀ A ⊆ ⋃₀ A₁ ∪ ⋃₀ A₂ := by
      rintro x ⟨e, he, hx⟩
      by_cases h : ∃ a, S.IsEdgeEndpoint e a ∧ LinkedByChain S W A v₀ a
      · exact Or.inl ⟨e, ⟨he, h⟩, hx⟩
      · exact Or.inr ⟨e, ⟨he, h⟩, hx⟩
    obtain ⟨x, -, ⟨f₁, hf₁, hx₁⟩, ⟨f₂, hf₂, hx₂⟩⟩ :=
      isPreconnected_closed_iff.1 hcon _ _ (hclosed _ fun e he => he.1)
        (hclosed _ fun e he => he.1) hcover hne₁ hne₂
    have hne : f₁ ≠ f₂ := by
      rintro rfl
      exact hf₂.2 hf₁.2
    obtain ⟨hend₁, hend₂⟩ := hmid f₁ f₂ (hedge _ hf₁.1) (hedge _ hf₂.1) hne x hx₁ hx₂
    obtain ⟨a, ha, hj⟩ := hf₁.2
    exact hf₂.2 ⟨x, hend₂, hstep f₁ hf₁.1 a x ha hend₁ hj⟩
  intro v hv
  obtain ⟨e, he, hend⟩ := (hW v).1 hv
  have h : ∃ a, S.IsEdgeEndpoint e a ∧ LinkedByChain S W A v₀ a := by
    by_contra h
    exact hempty e ⟨he, h⟩
  obtain ⟨a, ha, hj⟩ := h
  exact hstep e he a v ha hend hj
def PreconnectedLinked (Γ : Set S.Points) (x y : S.Points) : Prop :=
  ∃ t, t ⊆ Γ ∧ x ∈ t ∧ y ∈ t ∧ IsPreconnected t
theorem PreconnectedLinked.trans {Γ : Set S.Points} {x y z : S.Points}
    (h : PreconnectedLinked Γ x y) (h' : PreconnectedLinked Γ y z) : PreconnectedLinked Γ x z := by
  obtain ⟨t, ht, hx, hy, hp⟩ := h
  obtain ⟨t', ht', hy', hz, hp'⟩ := h'
  exact ⟨t ∪ t', union_subset ht ht', Or.inl hx, Or.inr hz, hp.union y hy hy' hp'⟩
theorem preconnectedLinked_of_chain (hK : LevelUnitPartitionEdgesCompactConnected)
    {A : Set (Set S.Points)} (hedge : ∀ a ∈ A, S.IsEdge a) {W : Set S.Points}
    (hWΓ : W ⊆ ⋃₀ A) (c : List S.Points) :
    ∀ x y, (∀ u ∈ c, u ∈ W) →
      c.IsChain (fun a b => ∃ e ∈ A, HasEndpoints S e a b) →
      c.head? = some x → c.getLast? = some y → PreconnectedLinked (⋃₀ A) x y := by
  induction c with
  | nil => intro x y _ _ h; simp at h
  | cons a l ih =>
    intro x y hW hc hh hl
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases l with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact ⟨{a}, singleton_subset_iff.2 (hWΓ (hW a (by simp))), rfl, rfl,
        isPreconnected_singleton⟩
    | cons b l' =>
      rw [List.isChain_cons_cons] at hc
      obtain ⟨⟨e, he, -, ha, hb⟩, hc'⟩ := hc
      have hee := hK S e (hedge e he)
      refine PreconnectedLinked.trans ⟨e, subset_sUnion_of_mem he, hee.2.2 a ha, hee.2.2 b hb,
        hee.2.1.isPreconnected⟩ (ih b y (fun u hu => hW u (List.mem_cons_of_mem _ hu)) hc' rfl ?_)
      rw [← hl]
      simp
theorem isConnected_of_chainConnected (hK : LevelUnitPartitionEdgesCompactConnected)
    (hend : ∀ e, S.IsEdge e → ∃ v, S.IsEdgeEndpoint e v)
    {A : Set (Set S.Points)} (hne : A.Nonempty) (hedge : ∀ a ∈ A, S.IsEdge a)
    {W : Set S.Points} (hW : ∀ v, v ∈ W ↔ ∃ e ∈ A, S.IsEdgeEndpoint e v)
    (hj : ∀ v ∈ W, ∀ v' ∈ W, LinkedByChain S W A v v') : IsConnected (⋃₀ A) := by
  have hWΓ : W ⊆ ⋃₀ A := by
    intro v hv
    obtain ⟨e, he, h⟩ := (hW v).1 hv
    exact ⟨e, he, (hK S e (hedge e he)).2.2 v h⟩
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨v₀, hv₀⟩ := hend e₀ (hedge e₀ he₀)
  have hv₀W : v₀ ∈ W := (hW v₀).2 ⟨e₀, he₀, hv₀⟩
  refine ⟨⟨v₀, hWΓ hv₀W⟩, isPreconnected_of_forall v₀ ?_⟩
  rintro y ⟨e, he, hy⟩
  obtain ⟨a, ha⟩ := hend e (hedge e he)
  have hee := hK S e (hedge e he)
  obtain ⟨c, hcW, hc, hh, hl⟩ := hj v₀ hv₀W a ((hW a).2 ⟨e, he, ha⟩)
  obtain ⟨t, ht, h₀, h₁, hp⟩ := PreconnectedLinked.trans
    (preconnectedLinked_of_chain hK hedge hWΓ c v₀ a hcW hc hh hl)
    (⟨e, subset_sUnion_of_mem he, hee.2.2 a ha, hy, hee.2.1.isPreconnected⟩ :
      PreconnectedLinked (⋃₀ A) a y)
  exact ⟨t, ht, h₀, h₁, hp⟩
theorem adjacentVerticesConnectEdgeGraphs_holds (hL : CubeLifts.Statement)
    (hG : EdgeGraphsDescribedByCubes)
    (hE : PartitionEdgeEndpoints)
    (hK : LevelUnitPartitionEdgesCompactConnected) :
    AdjacentVerticesConnectEdgeGraphs := by
  intro S
  obtain ⟨T, -, -, hV, -, hS⟩ := hL.2.2 S
  have hM : 0 < S.side := T.2.2.2.2.2.2.2.2.2.2
  have hpart : S.cubes = standardCubePartition S.params.L S.params.m S.index := T.2.2.1
  have hreg : IsPartitionRegion S.index S.fullRegion := ⟨S.cubes, hpart.le, rfl⟩
  obtain ⟨hdet, -, hmid, hcount, hcorner, -⟩ := hE S _ hreg
  obtain ⟨hvert, -, hedges, -, -, -⟩ := id hV
  have hcubes : ∀ Δ ∈ S.cubes, Δ ∈ partitionCubesIn S.index S.fullRegion := fun Δ hΔ =>
    ⟨hpart ▸ hΔ, subset_sUnion_of_mem hΔ⟩
  have hend : ∀ e, S.IsEdge e → ∃ v, S.IsEdgeEndpoint e v := by
    intro e he
    obtain ⟨w, hw, ν, rfl⟩ := (hedges e).1 he
    exact ⟨_, w, hw, ν, rfl, Or.inl rfl⟩
  have hendvert : ∀ e v, S.IsEdgeEndpoint e v → S.IsVertex v := by
    rintro e v ⟨w, hw, ν, -, rfl | rfl⟩
    · exact (hvert _).2 ⟨w, hw, rfl⟩
    · refine (hvert _).2 ⟨_, ?_, rfl⟩
      have := add_signedStep_mem hw ν (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
      rwa [signedStep_one] at this
  have hgraph : ∀ A : Set (Set S.Points), A.Nonempty → (∀ a ∈ A, S.IsEdge a) →
      S.IsGlobalEdgeGraph (⋃₀ A) := by
    intro A hne hA
    refine (hG S _ hreg).1.2.2 A hne fun e he => ?_
    obtain ⟨Δ, hΔ, h⟩ := hA e he
    exact ⟨Δ, hcubes Δ hΔ, h⟩
  have hverts : ∀ A : Set (Set S.Points), A.Finite → A.Nonempty →
      (∀ a ∈ A, S.IsEdge a) →
      S.graphEdges (⋃₀ A) = A ∧
        ∀ v, v ∈ S.graphVertices (⋃₀ A) ↔ ∃ e ∈ A, S.IsEdgeEndpoint e v := by
    intro A hfin hne hA
    have hAeq := (hcount _ A (hgraph A hne hA) hfin hne hA rfl).1
    refine ⟨hAeq, fun v => ⟨?_, ?_⟩⟩
    · rintro (⟨e, he, h⟩ | ⟨hv, hΓ⟩)
      · exact ⟨e, hAeq ▸ he, h⟩
      · have h0 := hcorner v hv
        rw [← hΓ, hAeq] at h0
        exact absurd h0 hne.ne_empty
    · rintro ⟨e, he, h⟩
      exact Or.inl ⟨e, hAeq.symm ▸ he, h⟩
  have hjoin : ∀ A : Set (Set S.Points), A.Finite → A.Nonempty →
      (∀ a ∈ A, S.IsEdge a) →
      (IsConnected (⋃₀ A) ↔
        ∀ v ∈ S.graphVertices (⋃₀ A), ∀ v' ∈ S.graphVertices (⋃₀ A),
          LinkedByChain S (S.graphVertices (⋃₀ A)) (S.graphEdges (⋃₀ A)) v v') := by
    intro A hfin hne hA
    obtain ⟨hAeq, hW⟩ := hverts A hfin hne hA
    rw [hAeq]
    constructor
    · intro hc v hv v' hv'
      exact chainConnected_of_isPreconnected hK hfin hA hmid hc.isPreconnected hW hv v' hv'
    · exact isConnected_of_chainConnected hK hend hne hA hW
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    ext v
    exact adjacent_proj_iff hM T hV hS hdet hw v
  · intro v hv
    refine ⟨?_, fun h => h.2.2.1 rfl⟩
    obtain ⟨w, hw, rfl⟩ := (hvert v).1 hv
    exact encard_adjacent_le_eight w fun v' => (adjacent_proj_iff hM T hV hS hdet hw v').1
  · intro A hfin hne hA
    exact ⟨hgraph A hne hA, hjoin A hfin hne hA⟩
  · rintro Γ ⟨hΓ, hcon⟩
    rcases (hG S _ hreg).1.1 Γ hΓ hcon.nonempty with ⟨Δ, hΔ, v, hv, rfl⟩ | ⟨E, hfin, hne, hE', rfl⟩
    · have hvv : S.IsVertex v := ⟨Δ, hpart ▸ hΔ.1, hv⟩
      have hV₁ : S.graphVertices {v} = {v} := by
        ext u
        constructor
        · rintro (⟨e, he, -⟩ | ⟨-, h⟩)
          · rw [hcorner v hvv] at he
            exact he.elim
          · exact (singleton_eq_singleton_iff.1 h).symm
        · rintro rfl
          exact Or.inr ⟨hvv, rfl⟩
      rw [hV₁]
      refine ⟨fun u hu => hu ▸ hvv, singleton_nonempty v, ?_⟩
      intro u hu u' hu'
      have h₁ : u = v := hu
      have h₂ : u' = v := hu'
      rw [h₁, h₂]
      exact ⟨[v], by simp, List.isChain_singleton _, rfl, rfl⟩
    · have hA : ∀ a ∈ E, S.IsEdge a := fun a ha => by
        obtain ⟨Δ, hΔ, h⟩ := hE' a ha
        exact ⟨Δ, hpart ▸ hΔ.1, h⟩
      obtain ⟨hAeq, hW⟩ := hverts E hfin hne hA
      have hjoined := (hjoin E hfin hne hA).1 hcon
      obtain ⟨e₀, he₀⟩ := hne
      obtain ⟨v₀, hv₀⟩ := hend e₀ (hA e₀ he₀)
      refine ⟨?_, ⟨v₀, (hW v₀).2 ⟨e₀, he₀, hv₀⟩⟩, ?_⟩
      · intro v hv
        obtain ⟨e, -, h⟩ := (hW v).1 hv
        exact hendvert e v h
      · intro v hv v' hv'
        obtain ⟨c, hcW, hc, hh, hl⟩ := hjoined v hv v' hv'
        refine ⟨c, hcW, hc.imp ?_, hh, hl⟩
        rintro a b ⟨e, he, hab, ha, hb⟩
        rw [hAeq] at he
        exact ⟨hendvert e a ha, hendvert e b hb, hab, e, hA e he, ha, hb⟩
end YangMills.Construction.PeriodicLattice.AdjacencyAndConnectedGraphs
end
