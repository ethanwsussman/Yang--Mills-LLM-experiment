import YangMills.Construction.Lattice.AdjacentVerticesAndConnectedEdgeGraphsProof
import YangMills.Construction.Lattice.CornersAndEdgesInTwoCoordinates
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.PeriodicLattice
namespace EdgeEndpoints
open CubeLifts (IsPeriodVector TorusInCubeUnits SiteAndCubeLifts
  VertexAndEdgeLifts EdgePointsInCube ShortVectorsNotPeriods IsCubeCentre)
variable {S : LevelUnitPartition}
theorem int_eq_zero_of_mul_mem_Ioo {M x : ℝ} (hM : 0 < M) {k : ℤ} (hx : x = M * (k : ℝ))
    (h1 : -M < x) (h2 : x < M) : k = 0 := by
  subst hx
  have ha : (-1 : ℝ) < k := by nlinarith
  have hb : (k : ℝ) < 1 := by nlinarith
  have ha' : (-1 : ℤ) < k := by exact_mod_cast ha
  have hb' : k < 1 := by exact_mod_cast hb
  omega
theorem proj_eq_iff (T : TorusInCubeUnits S) (w w' : Fin 4 → ℝ) :
    S.proj w = S.proj w' ↔ IsPeriodVector S (w - w') := by apply _root_.YangMills.Construction.PeriodicLattice.AdjacencyAndConnectedGraphs.proj_eq_iff <;> assumption
theorem proj_add_congr (T : TorusInCubeUnits S) {w w' : Fin 4 → ℝ}
    (h : S.proj w = S.proj w') (u : Fin 4 → ℝ) :
    S.proj (w + u) = S.proj (w' + u) := by apply _root_.YangMills.Construction.PeriodicLattice.AdjacencyAndConnectedGraphs.proj_add_congr <;> assumption
theorem add_period_mem_vertexSet {w r : Fin 4 → ℝ} (hw : w ∈ S.vertexSet)
    (hr : IsPeriodVector S r) : w + r ∈ S.vertexSet := by
  obtain ⟨a, ha⟩ := hr
  intro μ
  obtain ⟨b, hb⟩ := hw μ
  refine ⟨b + (S.cubeCount : ℤ) * a μ, ?_⟩
  simp only [Pi.add_apply, ha μ, hb]
  push_cast
  ring
theorem proj_mem_edgeAt (w : Fin 4 → ℝ) (ν : Fin 4) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ (S.side : ℝ)) : S.proj (w + t • coordVec ν) ∈ S.edgeAt w ν :=
  ⟨_, ⟨t, h0, h1, rfl⟩, rfl⟩
theorem edgeAt_congr (T : TorusInCubeUnits S) {w w' : Fin 4 → ℝ}
    (h : S.proj w = S.proj w') (ν : Fin 4) : S.edgeAt w ν = S.edgeAt w' ν := by
  have key : ∀ {a b : Fin 4 → ℝ}, S.proj a = S.proj b →
      S.edgeAt a ν ⊆ S.edgeAt b ν := by
    rintro a b hab _ ⟨_, ⟨t, h0, h1, rfl⟩, rfl⟩
    rw [proj_add_congr T hab]
    exact proj_mem_edgeAt b ν h0 h1
  exact Subset.antisymm (key h) (key h.symm)
theorem axis_eq_and_proj_eq_of_mem (T : TorusInCubeUnits S) {w w' : Fin 4 → ℝ}
    (hw : w ∈ S.vertexSet) (hw' : w' ∈ S.vertexSet) {ν ν' : Fin 4} {t : ℝ} (h0 : 0 < t)
    (h1 : t < (S.side : ℝ)) (hmem : S.proj (w + t • coordVec ν) ∈ S.edgeAt w' ν') :
    ν = ν' ∧ S.proj w = S.proj w' := by
  have hM : (0 : ℝ) < (S.side : ℝ) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hM⟩ := T
    exact_mod_cast hM
  obtain ⟨_, ⟨t', h0', h1', rfl⟩, heq⟩ := hmem
  obtain ⟨a, ha⟩ := (proj_eq_iff T _ _).mp heq.symm
  choose b hb using hw
  choose b' hb' using hw'
  have comp : ∀ μ, w μ + t * (coordVec ν) μ - (w' μ + t' * (coordVec ν') μ) =
      (S.cubeCount : ℝ) * (S.side : ℝ) * (a μ : ℝ) := by
    intro μ
    simpa using ha μ
  have hνν : ν = ν' := by
    by_contra hne
    have hc := comp ν
    simp only [coordVec, Pi.single_eq_same, Pi.single_eq_of_ne hne, mul_one, mul_zero,
      add_zero, hb ν, hb' ν] at hc
    have hk := int_eq_zero_of_mul_mem_Ioo (k := (S.cubeCount : ℤ) * a ν - (b ν - b' ν)) hM
      (x := t) (by push_cast; linarith) (by linarith) h1
    have : t = (S.side : ℝ) * (((S.cubeCount : ℤ) * a ν - (b ν - b' ν) : ℤ) : ℝ) := by
      push_cast
      linarith
    rw [hk] at this
    simp at this
    linarith
  subst hνν
  have htt : t = t' := by
    have hc := comp ν
    simp only [coordVec, Pi.single_eq_same, mul_one, hb ν, hb' ν] at hc
    have hx : t - t' = (S.side : ℝ) * (((S.cubeCount : ℤ) * a ν - (b ν - b' ν) : ℤ) : ℝ) := by
      push_cast
      linarith
    have hk := int_eq_zero_of_mul_mem_Ioo hM hx (by linarith) (by linarith)
    rw [hk] at hx
    simp at hx
    linarith
  subst htt
  refine ⟨rfl, (proj_eq_iff T _ _).mpr ⟨a, fun μ => ?_⟩⟩
  have hc := comp μ
  simp only [Pi.sub_apply]
  linarith
theorem edgeAt_eq_of_mem (T : TorusInCubeUnits S) {w w' : Fin 4 → ℝ}
    (hw : w ∈ S.vertexSet) (hw' : w' ∈ S.vertexSet) {ν ν' : Fin 4} {t : ℝ} (h0 : 0 < t)
    (h1 : t < (S.side : ℝ))
    (hmem : S.proj (w + t • coordVec ν) ∈ S.edgeAt w' ν') :
    S.edgeAt w ν = S.edgeAt w' ν' := by
  obtain ⟨rfl, h⟩ := axis_eq_and_proj_eq_of_mem T hw hw' h0 h1 hmem
  exact edgeAt_congr T h ν
theorem endpoints_ne (T : TorusInCubeUnits S) (V : ShortVectorsNotPeriods S)
    (w : Fin 4 → ℝ) (ν : Fin 4) :
    S.proj w ≠ S.proj (w + (S.side : ℝ) • coordVec ν) := by
  have hM : (0 : ℝ) < (S.side : ℝ) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hM⟩ := T
    exact_mod_cast hM
  intro h
  refine V.1 (w - (w + (S.side : ℝ) • coordVec ν)) ?_ ?_
    ((proj_eq_iff T _ _).mp h)
  · intro h0
    have := congrFun h0 ν
    simp [coordVec] at this
    exact hM.ne' (by exact_mod_cast this)
  · intro μ
    by_cases hμ : μ = ν
    · subst hμ
      right; right
      simp [coordVec]
    · left
      simp [coordVec, Pi.single_eq_of_ne hμ]
theorem isEdgeEndpoint_of_mem_of_ne (T : TorusInCubeUnits S) {w w' : Fin 4 → ℝ}
    (hw : w ∈ S.vertexSet) (hw' : w' ∈ S.vertexSet) {ν ν' : Fin 4}
    (hne : S.edgeAt w ν ≠ S.edgeAt w' ν') {x : S.Points} (hx : x ∈ S.edgeAt w ν)
    (hx' : x ∈ S.edgeAt w' ν') : S.IsEdgeEndpoint (S.edgeAt w ν) x := by
  obtain ⟨_, ⟨t, h0, h1, rfl⟩, rfl⟩ := hx
  rcases h0.eq_or_lt with rfl | h0
  · exact ⟨w, hw, ν, rfl, Or.inl (by simp)⟩
  rcases h1.eq_or_lt with rfl | h1
  · exact ⟨w, hw, ν, rfl, Or.inr rfl⟩
  exact absurd (edgeAt_eq_of_mem T hw hw' h0 h1 hx') hne
theorem edgeAt_subset_proj_closedBox (hM : (0 : ℝ) < (S.side : ℝ)) (c : Fin 4 → ℝ)
    {ε : Fin 4 → ℝ} {ν : Fin 4} (hε : LevelUnitPartition.IsSigns ε) (hν : ε ν = -1) :
    S.edgeAt (c + ((S.side : ℝ) / 2) • ε) ν ⊆ S.proj '' S.closedBox c := by
  rintro _ ⟨_, ⟨t, h0, h1, rfl⟩, rfl⟩
  refine ⟨_, fun μ => ?_, rfl⟩
  by_cases hμ : μ = ν
  · subst hμ
    simp only [coordVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      hν, mem_Icc]
    constructor <;> linarith
  · simp only [coordVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne hμ, mem_Icc]
    rcases hε μ with h | h <;> rw [h] <;> constructor <;> linarith
end EdgeEndpoints
open EdgeEndpoints in
theorem partitionEdgeEndpoints_holds
    (hLifts : CubeLifts.Statement)
    (hLiftsCommute : CubeVertexEdgeAgreement) :
    PartitionEdgeEndpoints := by
  intro S X hX
  obtain ⟨-, -, hAll⟩ := hLifts
  obtain ⟨T, -, LS, VE, PE, SV⟩ := hAll S
  have hM : (0 : ℝ) < (S.side : ℝ) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hM⟩ := T
    exact_mod_cast hM
  have hP : S.cubes = standardCubePartition S.params.L S.params.m S.index := T.2.2.1
  have hLift : ∀ x : S.Points, ∃ w, S.IsPointLift x w := T.2.2.2.2.2.2.1
  have hedge := VE.2.2.1
  have part1 : ∀ w ∈ S.vertexSet, ∀ w' ∈ S.vertexSet, ∀ ν ν' : Fin 4,
      S.edgeAt w ν = S.edgeAt w' ν' → ν = ν' ∧ S.proj w = S.proj w' := by
    intro w hw w' hw' ν ν' h
    refine axis_eq_and_proj_eq_of_mem T hw hw' (t := (S.side : ℝ) / 2) (by linarith)
      (by linarith) ?_
    rw [← h]
    exact proj_mem_edgeAt w ν (by linarith) (by linarith)
  refine ⟨part1, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨w, hw, ν, rfl⟩ := (hedge e).mp he
    have hset : {v | S.IsEdgeEndpoint (S.edgeAt w ν) v} =
        {S.proj w, S.proj (w + (S.side : ℝ) • coordVec ν)} := by
      ext v
      constructor
      · rintro ⟨w', hw', ν', he', hv⟩
        obtain ⟨rfl, h⟩ := part1 w hw w' hw' ν ν' he'
        rcases hv with rfl | rfl
        · exact Or.inl h.symm
        · exact Or.inr (proj_add_congr T h _).symm
      · rintro (rfl | rfl)
        · exact ⟨w, hw, ν, rfl, Or.inl rfl⟩
        · exact ⟨w, hw, ν, rfl, Or.inr rfl⟩
    rw [hset]
    exact ncard_pair (endpoints_ne T SV w ν)
  · intro e e' he he' hne x hx hx'
    obtain ⟨w, hw, ν, rfl⟩ := (hedge e).mp he
    obtain ⟨w', hw', ν', rfl⟩ := (hedge e').mp he'
    exact ⟨isEdgeEndpoint_of_mem_of_ne T hw hw' hne hx hx',
      isEdgeEndpoint_of_mem_of_ne T hw' hw hne.symm hx' hx⟩
  · intro Γ' A _ _ _ hA hΓ
    have hedges : S.graphEdges Γ' = A := by
      ext e
      constructor
      · rintro ⟨he, hsub⟩
        obtain ⟨w, hw, ν, rfl⟩ := (hedge e).mp he
        have hm := hsub (proj_mem_edgeAt (S := S) w ν (t := (S.side : ℝ) / 2) (by linarith)
          (by linarith))
        rw [hΓ] at hm
        obtain ⟨a, haA, hma⟩ := hm
        obtain ⟨w', hw', ν', rfl⟩ := (hedge a).mp (hA a haA)
        rwa [edgeAt_eq_of_mem T hw hw' (by linarith) (by linarith) hma]
      · intro he
        exact ⟨hA e he, hΓ ▸ subset_sUnion_of_mem he⟩
    refine ⟨hedges, ?_⟩
    have hset : {e | (∃ Q ∈ standardCubePartition S.params.L S.params.m S.index,
        IsCubeEdge S.index e Q) ∧ e ⊆ Γ'} = S.graphEdges Γ' := by
      ext e
      constructor
      · rintro ⟨⟨Q, hQ, hE⟩, hs⟩
        have hQ' : Q ∈ S.cubes := hP ▸ hQ
        exact ⟨⟨Q, hQ', ((hLiftsCommute S Q hQ').2 e).mp hE⟩, hs⟩
      · rintro ⟨⟨Q, hQ, hE⟩, hs⟩
        exact ⟨⟨Q, hP ▸ hQ, ((hLiftsCommute S Q hQ).2 e).mpr hE⟩, hs⟩
    unfold edgeCount
    rw [hset, hedges]
  · intro v _
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro e ⟨he, hsub⟩
    obtain ⟨w, hw, ν, rfl⟩ := (hedge e).mp he
    have h1 : S.proj w ∈ ({v} : Set S.Points) := by
      have := hsub (proj_mem_edgeAt (S := S) w ν (t := 0) le_rfl hM.le)
      simpa using this
    have h2 : S.proj (w + (S.side : ℝ) • coordVec ν) ∈ ({v} : Set S.Points) :=
      hsub (proj_mem_edgeAt (S := S) w ν hM.le le_rfl)
    exact endpoints_ne T SV w ν (h1.trans h2.symm)
  · intro e he
    constructor
    · intro hsub
      obtain ⟨w, hw, ν, rfl⟩ := (hedge e).mp he
      obtain ⟨C, hC, rfl⟩ := hX
      obtain ⟨Q, hQC, hmQ⟩ := hsub (proj_mem_edgeAt (S := S) w ν (t := (S.side : ℝ) / 2)
        (by linarith) (by linarith))
      have hQ := hC hQC
      obtain ⟨y, rfl⟩ := hQ
      obtain ⟨c, hc⟩ := hLift (y : S.Points)
      have hcube := LS.2.1 y c hc
      have hcc : CubeLifts.IsCubeCentre S c := (LS.1 c).mp ⟨y, hc⟩
      rw [hcube] at hmQ
      obtain ⟨z, hz, hzeq⟩ := hmQ
      have hper := (proj_eq_iff T _ _).mp hzeq
      set r := z - (w + ((S.side : ℝ) / 2) • coordVec ν) with hr
      have hw' : w + r ∈ S.vertexSet := add_period_mem_vertexSet hw hper
      have hz' : (w + r) + ((S.side : ℝ) / 2) • coordVec ν = z := by
        rw [hr]
        abel
      have hE := (PE c (w + r) ν ((S.side : ℝ) / 2) hcc hw' (by linarith) (by linarith)
        (hz'.symm ▸ hz)).2 (by linarith) (by linarith)
      have hee : S.edgeAt (w + r) ν = S.edgeAt w ν := by
        refine edgeAt_congr T ((proj_eq_iff T _ _).mpr ?_) ν
        have : w + r - w = r := by abel
        rwa [this]
      rw [hee, ← hcube] at hE
      exact ⟨cubeAround y, ⟨⟨y, rfl⟩, subset_sUnion_of_mem hQC⟩, hE.2⟩
    · rintro ⟨Δ, ⟨-, hsub⟩, y, rfl, c, hc, ε, ν, hε, hν, rfl⟩
      have hcube := LS.2.1 y c hc
      exact ((edgeAt_subset_proj_closedBox hM c hε hν).trans hcube.symm.subset).trans hsub
end YangMills.Construction.PeriodicLattice
