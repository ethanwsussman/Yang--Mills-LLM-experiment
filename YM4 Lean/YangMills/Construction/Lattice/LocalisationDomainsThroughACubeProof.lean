import YangMills.Construction.Graphs.ClosedWalkThroughAllVertices
import YangMills.Construction.Lattice.CosetsCoordinatesAndDistances
import YangMills.Construction.Lattice.CubesVerticesAndEdgesOfThePartition
import YangMills.Construction.Lattice.LocalisationDomainsThroughACube
import YangMills.Construction.Lattice.SidesOfTheCubesAndTheLinearSize
import YangMills.Construction.Lattice.TreeOfALocalisationDomain
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice
noncomputable section
namespace TorusBound.RegionsThroughCube
variable (T : Setup)
def cubeStep (j : ℕ) (k : Fin 4 × Bool) (u : T.Torus) : T.Torus :=
  T.addVec u ((if k.2 then T.physicalCubeSide j else -T.physicalCubeSide j) • coordVec k.1)
def stepWalk (j : ℕ) {n : ℕ} (r : T.Torus) (s : Fin n → Fin 4 × Bool) : ℕ → T.Torus
  | 0 => r
  | t + 1 => if h : t < n then cubeStep T j (s ⟨t, h⟩) (stepWalk j r s t) else stepWalk j r s t
def stepWalkPoints (j : ℕ) {n : ℕ} (r : T.Torus) (s : Fin n → Fin 4 × Bool) : Set T.Torus :=
  {x | ∃ t ≤ n, stepWalk T j r s t = x}
variable {T}
theorem exists_eq_stepWalk (j n : ℕ) (u : ℕ → T.Torus)
    (h : ∀ t < n, ∃ k, u (t + 1) = cubeStep T j k (u t)) :
    ∃ s : Fin n → Fin 4 × Bool, ∀ t ≤ n, u t = stepWalk T j (u 0) s t := by
  classical
  have h' : ∀ t : Fin n, ∃ k, u ((t : ℕ) + 1) = cubeStep T j k (u t) := fun t => h t t.2
  choose s hs using h'
  refine ⟨s, fun t => ?_⟩
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hlt : t < n := ht
    have := hs ⟨t, hlt⟩
    simp only at this
    rw [this, ih hlt.le]
    simp [stepWalk, hlt]
theorem encard_le_two_pow_of_cubes_subset {L m : ℕ} {i : ℤ} {K : Set (Set (FourTorus L m))}
    {n : ℕ} (hK : K.encard ≤ n) {F : Set (Set (FourTorus L m))}
    (hF : ∀ X ∈ F, IsPartitionRegion i X ∧ partitionCubesIn i X ⊆ K) :
    F.encard ≤ ((2 ^ n : ℕ) : ℕ∞) := by
  classical
  have hfin : K.Finite := finite_of_encard_le_coe hK
  have hsub : F ⊆ (fun S : Finset (Set (FourTorus L m)) => ⋃₀ (S : Set (Set (FourTorus L m)))) ''
      (hfin.toFinset.powerset : Set (Finset (Set (FourTorus L m)))) := by
    intro X hX
    obtain ⟨⟨C, hC, rfl⟩, hcubes⟩ := hF X hX
    have hf : (partitionCubesIn i (⋃₀ C)).Finite := hfin.subset hcubes
    refine ⟨hf.toFinset, ?_, ?_⟩
    · simp only [Finset.coe_powerset, mem_preimage, mem_powerset_iff]
      intro P hP
      simpa using hcubes (by simpa using hP)
    · simp only [Set.Finite.coe_toFinset]
      apply Subset.antisymm
      · rintro x ⟨P, hP, hx⟩
        exact hP.2 hx
      · rintro x ⟨P, hP, hx⟩
        exact ⟨P, ⟨hC hP, subset_sUnion_of_mem hP⟩, hx⟩
  have hcard : hfin.toFinset.card ≤ n := by
    have : ((hfin.toFinset.card : ℕ) : ℕ∞) ≤ n := by
      rw [← encard_coe_eq_coe_finsetCard]
      simpa using hK
    exact_mod_cast this
  calc F.encard ≤ _ := encard_le_encard hsub
    _ ≤ ((hfin.toFinset.powerset : Finset _) : Set (Finset (Set (FourTorus L m)))).encard :=
        encard_image_le _ _
    _ = ((2 ^ hfin.toFinset.card : ℕ) : ℕ∞) := by
        rw [encard_coe_eq_coe_finsetCard, Finset.card_powerset]
    _ ≤ ((2 ^ n : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hcard
theorem exists_chain_of_reflTransGen {α : Type*} {R : α → α → Prop} {x y : α}
    (hr : Relation.ReflTransGen R x y) :
    ∃ (n : ℕ) (p : ℕ → α), p 0 = x ∧ p n = y ∧ ∀ i < n, R (p i) (p (i + 1)) := by
  induction hr with
  | refl => exact ⟨0, fun _ => x, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, p, h0, hn, hs⟩ := ih
    refine ⟨n + 1, fun i => if i ≤ n then p i else c, by simpa using h0, by simp, ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i n with hlt | hge
    · have h₁ : i ≤ n := hlt.le
      have h₂ : i + 1 ≤ n := hlt
      simpa [h₁, h₂] using hs i hlt
    · have hi' : i = n := by omega
      subst hi'
      simpa [hn] using hbc
theorem pair_eq_endpoints_of_joins {j : ℕ} {hj : j ≤ T.K} {h : T.LevelFits j}
    {Γ A : Set T.Torus} {x y : T.Torus} (hl : T.TreeGraphJoins hj h Γ A x y) :
    ({x, y} : Set T.Torus) = ({z | (T.levelUnitPartition hj h).IsEdgeEndpoint A z} : Set T.Torus) :=
  hl.2.symm
theorem treeGraphJoins_symm {j : ℕ} {hj : j ≤ T.K} {h : T.LevelFits j} {Γ A : Set T.Torus}
    {x y : T.Torus} (hl : T.TreeGraphJoins hj h Γ A x y) : T.TreeGraphJoins hj h Γ A y x := by
  have he : ({z | (T.levelUnitPartition hj h).IsEdgeEndpoint A z} : Set T.Torus) =
      ({y, x} : Set T.Torus) := (pair_eq_endpoints_of_joins hl).symm.trans (pair_comm x y)
  exact ⟨hl.1, he⟩
def treeGraph {j : ℕ} (hj : j ≤ T.K) (h : T.LevelFits j) (Γ : Set T.Torus)
    (hdiff : T.TreeGraphLoopless hj h Γ) : Graph T.Torus (Set T.Torus) where
  vertexSet := T.treeGraphVertices hj h Γ
  IsLink A u u' := T.TreeGraphJoins hj h Γ A u u'
  edgeSet := T.treeGraphEdges hj h Γ
  isLink_symm := fun _ _ => ⟨fun _ _ hl => treeGraphJoins_symm hl⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro A x y v w h₁ h₂
    have hp : ({x, y} : Set T.Torus) = {v, w} :=
      (pair_eq_endpoints_of_joins h₁).trans (pair_eq_endpoints_of_joins h₂).symm
    have hx : x ∈ ({v, w} : Set T.Torus) := hp ▸ mem_insert x {y}
    simpa using hx
  edge_mem_iff_exists_isLink := by
    intro A
    constructor
    · intro hA
      obtain ⟨u, u', -, hl⟩ := hdiff A hA
      exact ⟨u, u', hl⟩
    · rintro ⟨u, u', hl⟩
      exact hl.1
  left_mem_of_isLink := by
    intro A x y hl
    refine Or.inl ⟨A, hl.1, ?_⟩
    exact show x ∈ ({z | (T.levelUnitPartition hj h).IsEdgeEndpoint A z} : Set T.Torus) from
      pair_eq_endpoints_of_joins hl ▸ mem_insert x {y}
theorem exists_cubeStep_of_joins (hlat : Coordinates.CosetsAndDistancesStatement) {j : ℕ}
    (hj : j ≤ T.K) (h : T.LevelFits j) {Γ A : Set T.Torus} {x y : T.Torus}
    (hl : T.TreeGraphJoins hj h Γ A x y) : ∃ k, y = cubeStep T j k x := by
  obtain ⟨-, -, -, -, -, hEdges, -, -, hEnds, -⟩ := hlat T j hj h
  have hA : T.IsLevelEdge hj h A := hl.1.1
  obtain ⟨w, ν, hw, rfl⟩ := (hEdges A).1 hA
  have hpair : ({x, y} : Set T.Torus) = {T.torusCover w,
      T.torusCover (w + T.physicalCubeSide j • coordVec ν)} :=
    (pair_eq_endpoints_of_joins hl).trans (hEnds w ν hw).1
  rw [pair_eq_pair_iff] at hpair
  rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine ⟨(ν, true), ?_⟩
    have hlift : T.IsLiftOfPoint x w := h₁.symm
    simp only [cubeStep, if_true]
    rw [Setup.addVec_eq_torusCover_add hlift, h₂]
  · refine ⟨(ν, false), ?_⟩
    have hlift : T.IsLiftOfPoint x (w + T.physicalCubeSide j • coordVec ν) := h₁.symm
    simp only [cubeStep, Bool.false_eq_true, if_false]
    rw [Setup.addVec_eq_torusCover_add hlift, h₂]
    congr 1
    rw [neg_smul, add_neg_cancel_right]
theorem isLevelVertex_of_mem_treeGraphVertices (hlat : Coordinates.CosetsAndDistancesStatement)
    {j : ℕ} (hj : j ≤ T.K) (h : T.LevelFits j) {Γ : Set T.Torus} {v : T.Torus}
    (hv : v ∈ T.treeGraphVertices hj h Γ) : T.IsLevelVertex hj h v := by
  obtain ⟨-, -, -, -, hVert, -, hOne, hCoord, -⟩ := hlat T j hj h
  rcases hv with ⟨e, he, hend⟩ | ⟨hv, -⟩
  · have hE : T.IsLevelEdge hj h e := he.1
    obtain ⟨ν₀, hdir, -⟩ := hOne e hE
    obtain ⟨hother, hown⟩ := hCoord e ν₀ hE hdir
    have hmem : v ∈ e := by
      obtain ⟨w, -, ν, rfl, hv⟩ := hend
      rcases hv with rfl | rfl
      · exact ⟨w, ⟨0, le_rfl, by positivity, by simp⟩, rfl⟩
      · exact ⟨_, ⟨_, by positivity, le_rfl, rfl⟩, rfl⟩
    refine (hVert v).2 fun μ => ?_
    by_cases hμ : μ = ν₀
    · subst hμ
      exact (hown v hmem).2 hend
    · exact (hother μ hμ).2 v hmem
  · exact hv
theorem exists_minimal_edgeTree (hpres : CubeSidesAndLinearSize) {d : DomainKind}
    {j : ℕ} (hj : j ≤ T.K) (h : T.LevelFits j) {X Q : Set T.Torus}
    (hX : X ∈ T.regionsBy d j) (hQ : Q ∈ partitionCubesIn (T.cubeScaleIndex j) X) :
    ∃ n : ℕ, T.extent j X = (n : ℝ) ∧ ∃ Γ : Set T.Torus,
      IsEdgeTreeWithCount (T.levelUnitPartition hj h) X Γ n ∧
      ∀ Q' ∈ partitionCubesIn (T.cubeScaleIndex j) X, GraphIntersects Γ Q' := by
  obtain ⟨-, -, -, -, n, hn, hleast⟩ := ((hpres T j hj).2 h).2 d X hX |>.1 ⟨Q, hQ⟩
  obtain ⟨Γ, hΓ, hmeet⟩ := hleast.1
  exact ⟨n, hn, Γ, hΓ, hmeet⟩
theorem exists_corner_and_walk_covering (htree : LocalisationDomainTreeClaim)
    (hpres : CubeSidesAndLinearSize)
    (hgraph : Graphs.ExistsClosedWalkThroughAllVertices)
    (hlat : Coordinates.CosetsAndDistancesStatement)
    (hcubes : PartitionCells.Holds)
    {d : DomainKind} {j : ℕ} (hj : j ≤ T.K) (h : T.LevelFits j) {Q X : Set T.Torus}
    (hQ : Q ∈ T.cubesAt j) (hX : X ∈ T.regionsBy d j) (hQX : Q ⊆ X) {E : ℕ}
    (hE : T.extent j X = (E : ℝ)) :
    ∃ r, (T.levelUnitPartition hj h).IsCornerOf r Q ∧ ∃ s : Fin (2 * E) → Fin 4 × Bool,
      partitionCubesIn (T.cubeScaleIndex j) X ⊆
        (T.levelUnitPartition hj h).cubesMeeting (stepWalkPoints T j r s) ∧
      ((T.levelUnitPartition hj h).cubesMeeting (stepWalkPoints T j r s)).encard ≤
        ((16 * (E + 1) : ℕ) : ℕ∞) := by
  have hcube : Q ∈ partitionCubesIn (T.cubeScaleIndex j) X := ⟨hQ, hQX⟩
  obtain ⟨n, hn, Γ, hΓ, hmeet⟩ := exists_minimal_edgeTree hpres hj h hX hcube
  obtain rfl : n = E := by
    have : (n : ℝ) = E := hn.symm.trans hE
    exact_mod_cast this
  obtain ⟨⟨hconn, hdiff, hV, -⟩, hcov, hK, hKcard⟩ :=
    (htree T j hj h d X hX).1 n Γ ⟨Q, hcube⟩ hn.symm hΓ hmeet
  obtain ⟨r, hrV, hrQ⟩ := hcov Q hcube
  have hVfin : (T.treeGraphVertices hj h Γ).Finite :=
    finite_of_encard_le_coe (k := n + 1) (by simpa using hV)
  have hEfin : (T.treeGraphEdges hj h Γ).Finite := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have hempty : T.treeGraphEdges hj h Γ = ∅ := by
        refine eq_empty_of_forall_notMem fun A hA => ?_
        obtain ⟨u, u', hne, hl⟩ := hdiff A hA
        have hu : u ∈ T.treeGraphVertices hj h Γ :=
          (treeGraph hj h Γ hdiff).left_mem_of_isLink hl
        have hu' : u' ∈ T.treeGraphVertices hj h Γ :=
          (treeGraph hj h Γ hdiff).left_mem_of_isLink (treeGraphJoins_symm hl)
        have h1 : (T.treeGraphVertices hj h Γ).encard ≤ 1 := by simpa [h0] using hV
        exact hne (encard_le_one_iff.1 h1 u u' hu hu')
      rw [hempty]
      exact finite_empty
    · refine finite_of_ncard_pos ?_
      have : (T.treeGraphEdges hj h Γ).ncard = n := hΓ.2
      omega
  have hloop : (treeGraph hj h Γ hdiff).Loopless := by
    refine ⟨fun A x hl => ?_⟩
    have hl' : T.TreeGraphJoins hj h Γ A x x := hl
    obtain ⟨u, u', hne, hu⟩ := hdiff A hl'.1
    have hp : ({u, u'} : Set T.Torus) = {x, x} :=
      (pair_eq_endpoints_of_joins hu).trans (pair_eq_endpoints_of_joins hl').symm
    rw [pair_eq_pair_iff] at hp
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hne (h₁.trans h₂.symm)
    · exact hne (h₁.trans h₂.symm)
  have hconnG : Graphs.MultigraphPathConnected (treeGraph hj h Γ hdiff) := by
    intro x hx y hy
    obtain ⟨l, p, h0, hl, hs⟩ := exists_chain_of_reflTransGen (hconn x hx y hy)
    exact ⟨l, p, h0, hl, fun i hi => hs i hi⟩
  obtain ⟨-, u, hu0, -, hmem, hall, hadj⟩ :=
    hgraph T.Torus (Set T.Torus) (treeGraph hj h Γ hdiff) hVfin hEfin hloop hconnG n hΓ.2 r hrV
  have hcorner : (T.levelUnitPartition hj h).IsCornerOf r Q := by
    obtain ⟨c, rfl⟩ := hQ
    exact (((hcubes T j hj h).1.1 c r
      (isLevelVertex_of_mem_treeGraphVertices hlat hj h hrV)).2).1 hrQ
  have hsteps : ∀ t < 2 * n, ∃ k, u (t + 1) = cubeStep T j k (u t) := by
    intro t ht
    obtain ⟨A, hl⟩ := hadj (t + 1) (by omega) (by omega)
    have hl' : T.TreeGraphJoins hj h Γ A (u t) (u (t + 1)) := hl
    exact exists_cubeStep_of_joins hlat hj h hl'
  obtain ⟨s, hs⟩ := exists_eq_stepWalk j (2 * n) u hsteps
  rw [hu0] at hs
  have hterms : stepWalkPoints T j r s = T.treeGraphVertices hj h Γ := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [← hs t ht]
      exact hmem t ht
    · intro hx
      obtain ⟨t, ht, rfl⟩ := hall x hx
      exact ⟨t, ht, (hs t ht).symm⟩
  have hKeq : (T.levelUnitPartition hj h).cubesMeeting (stepWalkPoints T j r s) =
      (T.levelUnitPartition hj h).cubesMeeting (T.treeGraphVertices hj h Γ) :=
    congrArg _ hterms
  refine ⟨r, hcorner, s, ?_, ?_⟩
  · rw [hKeq]
    exact fun Q' hQ' => hK Q' hQ'
  · rw [hKeq]
    push_cast
    exact hKcard
theorem isPartitionRegion_of_mem_regionsBy {d : DomainKind} {j : ℕ} {X : Set T.Torus}
    (hX : X ∈ T.regionsBy d j) : IsPartitionRegion (T.cubeScaleIndex j) X := by
  cases d
  · exact hX.2.1
  · exact hX.2.1
theorem encard_regions_of_extent_le (htree : LocalisationDomainTreeClaim)
    (hpres : CubeSidesAndLinearSize)
    (hgraph : Graphs.ExistsClosedWalkThroughAllVertices)
    (hlat : Coordinates.CosetsAndDistancesStatement)
    (hcubes : PartitionCells.Holds)
    (d : DomainKind) {j : ℕ} (hj : j ≤ T.K) (h : T.LevelFits j) {Q : Set T.Torus}
    (hQ : Q ∈ T.cubesAt j) (E : ℕ) :
    {X | X ∈ T.regionsContaining d j Q ∧ T.extent j X = (E : ℝ)}.encard ≤
      (Setup.treeCountBound E : ℕ∞) := by
  classical
  have h16 : {v : T.Torus | (T.levelUnitPartition hj h).IsCornerOf v Q}.encard = 16 :=
    (hcubes T j hj h).1.2.1 Q hQ
  have hCfin : {v : T.Torus | (T.levelUnitPartition hj h).IsCornerOf v Q}.Finite :=
    finite_of_encard_eq_coe (k := 16) (by simpa using h16)
  have hCcard : hCfin.toFinset.card = 16 := by
    have : ((hCfin.toFinset.card : ℕ) : ℕ∞) = 16 := by
      rw [← encard_coe_eq_coe_finsetCard]
      simpa using h16
    exact_mod_cast this
  let K : T.Torus × (Fin (2 * E) → Fin 4 × Bool) → Set (Set T.Torus) := fun i =>
    (T.levelUnitPartition hj h).cubesMeeting (stepWalkPoints T j i.1 i.2)
  let F : T.Torus × (Fin (2 * E) → Fin 4 × Bool) → Set (Set T.Torus) := fun i =>
    {X | (K i).encard ≤ ((16 * (E + 1) : ℕ) : ℕ∞) ∧ IsPartitionRegion (T.cubeScaleIndex j) X ∧
      partitionCubesIn (T.cubeScaleIndex j) X ⊆ K i}
  let I : Finset (T.Torus × (Fin (2 * E) → Fin 4 × Bool)) := hCfin.toFinset ×ˢ Finset.univ
  have hsub : {X | X ∈ T.regionsContaining d j Q ∧ T.extent j X = (E : ℝ)} ⊆
      ⋃ i ∈ I, F i := by
    rintro X ⟨⟨hX, hQX⟩, hE⟩
    obtain ⟨r, hr, s, hcub, hcard⟩ :=
      exists_corner_and_walk_covering htree hpres hgraph hlat hcubes hj h hQ hX hQX hE
    refine mem_iUnion₂.2 ⟨(r, s), ?_, hcard, isPartitionRegion_of_mem_regionsBy hX, hcub⟩
    simp only [I, Finset.mem_product, Finset.mem_univ, and_true]
    exact hCfin.mem_toFinset.2 hr
  have hF : ∀ i, (F i).encard ≤ ((2 ^ (16 * (E + 1)) : ℕ) : ℕ∞) := by
    intro i
    by_cases hK : (K i).encard ≤ ((16 * (E + 1) : ℕ) : ℕ∞)
    · exact encard_le_two_pow_of_cubes_subset (i := T.cubeScaleIndex j) hK fun X hX => hX.2
    · have : F i = ∅ := eq_empty_of_forall_notMem fun X hX => hK hX.1
      rw [this]
      simp
  calc _ ≤ (⋃ i ∈ I, F i).encard := encard_le_encard hsub
    _ ≤ ∑ i ∈ I, (F i).encard := I.set_encard_biUnion_le F
    _ ≤ ∑ _i ∈ I, ((2 ^ (16 * (E + 1)) : ℕ) : ℕ∞) := Finset.sum_le_sum fun i _ => hF i
    _ = (Setup.treeCountBound E : ℕ∞) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [I, Finset.card_product, hCcard, Finset.card_univ, Fintype.card_fun,
          Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Setup.treeCountBound]
        push_cast
        norm_num
theorem treeCountBound_eq (E : ℕ) :
    (Setup.treeCountBound E : ℝ) =
      2 ^ 20 * Real.exp (PolymerActivities.DomainCounting.countingRate * (E : ℝ)) := by
  have hN : Setup.treeCountBound E = 2 ^ 20 * 2 ^ (22 * E) := by
    calc Setup.treeCountBound E
        = 2 ^ 4 * (2 ^ 3) ^ (2 * E) * 2 ^ (16 * (E + 1)) := by
          norm_num [Setup.treeCountBound]
      _ = 2 ^ (4 + 3 * (2 * E) + 16 * (E + 1)) := by
          rw [← pow_mul, ← pow_add, ← pow_add]
      _ = 2 ^ (20 + 22 * E) := by
          congr 1
          ring
      _ = 2 ^ 20 * 2 ^ (22 * E) := pow_add _ _ _
  have hexp : Real.exp (PolymerActivities.DomainCounting.countingRate * (E : ℝ)) =
      2 ^ (22 * E) := by
    have : PolymerActivities.DomainCounting.countingRate * (E : ℝ) =
        ((22 * E : ℕ) : ℝ) * Real.log 2 := by
      simp only [PolymerActivities.DomainCounting.countingRate]
      push_cast
      ring
    rw [this, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hN, hexp]
  push_cast
  ring
theorem tail_sum_le (htree : LocalisationDomainTreeClaim)
    (hpres : CubeSidesAndLinearSize)
    (hgraph : Graphs.ExistsClosedWalkThroughAllVertices)
    (hlat : Coordinates.CosetsAndDistancesStatement)
    (hcubes : PartitionCells.Holds)
    (d : DomainKind) {j : ℕ} (hj : j ≤ T.K) (h : T.LevelFits j) {Q : Set T.Torus}
    (hQ : Q ∈ T.cubesAt j) {κ' D : ℝ}
    (hκ : PolymerActivities.DomainCounting.countingRate < κ') :
    ∑ᶠ X ∈ {X | X ∈ T.regionsContaining d j Q ∧ D ≤ T.extent j X},
        Real.exp (-κ' * T.extent j X) ≤
      PolymerActivities.DomainCounting.rateSum κ' *
        Real.exp (-(κ' - PolymerActivities.DomainCounting.countingRate) * D) := by
  classical
  obtain ⟨-, -, -, -, hfinD⟩ := ((hpres T j hj).2 h).1
  have hA : {X | X ∈ T.regionsContaining d j Q ∧ D ≤ T.extent j X}.Finite :=
    (hfinD d).subset fun X hX => hX.1.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hA]
  set Af := hA.toFinset with hAf
  let g : Set T.Torus → ℕ := fun X => ⌊T.extent j X⌋₊
  have hg : ∀ X ∈ Af, T.extent j X = (g X : ℝ) := by
    intro X hX
    obtain ⟨⟨hXD, hQX⟩, -⟩ := hA.mem_toFinset.1 hX
    obtain ⟨n, hn, -⟩ :=
      exists_minimal_edgeTree hpres hj h hXD (show Q ∈ partitionCubesIn _ X from ⟨hQ, hQX⟩)
    simp only [g, hn, Nat.floor_natCast]
  set E₀ := ⌈D⌉₊ with hE₀
  set N := Af.sup g + 1 with hN
  have hmaps : ∀ X ∈ Af, g X ∈ Finset.Ico E₀ N := by
    intro X hX
    refine Finset.mem_Ico.2 ⟨Nat.ceil_le.2 ?_, Nat.lt_succ_of_le (Finset.le_sup hX)⟩
    rw [← hg X hX]
    exact (hA.mem_toFinset.1 hX).2
  set ρ := Real.exp (PolymerActivities.DomainCounting.countingRate - κ') with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hfibre : ∀ n ∈ Finset.Ico E₀ N,
      ∑ X ∈ Af with g X = n, Real.exp (-κ' * T.extent j X) ≤ 2 ^ 20 * ρ ^ n := by
    intro n _
    have hterm : ∀ X ∈ Af.filter (fun X => g X = n),
        Real.exp (-κ' * T.extent j X) = Real.exp (-κ' * (n : ℝ)) := by
      intro X hX
      obtain ⟨hXA, hXn⟩ := Finset.mem_filter.1 hX
      rw [hg X hXA, hXn]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Af.filter fun X => g X = n).card : ℕ) : ℝ) ≤
        (Setup.treeCountBound n : ℝ) := by
      have hsub : (((Af.filter fun X => g X = n) : Finset _) : Set (Set T.Torus)) ⊆
          {X | X ∈ T.regionsContaining d j Q ∧ T.extent j X = (n : ℝ)} := by
        intro X hX
        obtain ⟨hXA, hXn⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hX)
        refine ⟨(hA.mem_toFinset.1 hXA).1, ?_⟩
        rw [hg X hXA, hXn]
      have hle : (((Af.filter fun X => g X = n).card : ℕ) : ℕ∞) ≤
          (Setup.treeCountBound n : ℕ∞) := by
        rw [← encard_coe_eq_coe_finsetCard]
        exact (encard_le_encard hsub).trans
          (encard_regions_of_extent_le htree hpres hgraph hlat hcubes d hj h hQ n)
      exact_mod_cast hle
    have hpow : Real.exp (PolymerActivities.DomainCounting.countingRate * (n : ℝ)) *
        Real.exp (-κ' * (n : ℝ)) = ρ ^ n := by
      rw [← Real.exp_add, hρ, ← Real.exp_nat_mul]
      congr 1
      ring
    calc _ ≤ (Setup.treeCountBound n : ℝ) * Real.exp (-κ' * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = 2 ^ 20 * ρ ^ n := by
          rw [treeCountBound_eq, mul_assoc, hpow]
  have hgeom : ∑ n ∈ Finset.Ico E₀ N, ρ ^ n ≤ ρ ^ E₀ / (1 - ρ) :=
    geom_sum_Ico_le_of_lt_one hρ0.le hρ1
  have hdecay : ρ ^ E₀ ≤
      Real.exp (-(κ' - PolymerActivities.DomainCounting.countingRate) * D) := by
    rw [hρ, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hDE : D ≤ (E₀ : ℝ) := Nat.le_ceil D
    nlinarith [sub_pos.2 hκ]
  have h1ρ : 0 < 1 - ρ := by linarith
  calc ∑ X ∈ Af, Real.exp (-κ' * T.extent j X)
      = ∑ n ∈ Finset.Ico E₀ N, ∑ X ∈ Af with g X = n, Real.exp (-κ' * T.extent j X) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ n ∈ Finset.Ico E₀ N, 2 ^ 20 * ρ ^ n := Finset.sum_le_sum hfibre
    _ = 2 ^ 20 * ∑ n ∈ Finset.Ico E₀ N, ρ ^ n := by rw [Finset.mul_sum]
    _ ≤ 2 ^ 20 * (Real.exp (-(κ' - PolymerActivities.DomainCounting.countingRate) * D) /
          (1 - ρ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hgeom.trans (div_le_div_of_nonneg_right hdecay h1ρ.le)
    _ ≤ PolymerActivities.DomainCounting.rateSum κ' *
          Real.exp (-(κ' - PolymerActivities.DomainCounting.countingRate) * D) := by
        have hpos : 0 ≤ Real.exp (-(κ' - PolymerActivities.DomainCounting.countingRate) * D) *
            (1 - ρ)⁻¹ :=
          mul_nonneg (Real.exp_pos _).le (inv_pos.2 h1ρ).le
        simp only [PolymerActivities.DomainCounting.rateSum, ← hρ, div_eq_mul_inv]
        nlinarith [hpos]
theorem countAndTailBound_holds (htree : LocalisationDomainTreeClaim)
    (hpres : CubeSidesAndLinearSize)
    (hgraph : Graphs.ExistsClosedWalkThroughAllVertices)
    (hlat : Coordinates.CosetsAndDistancesStatement)
    (hcubes : PartitionCells.Holds) : CountAndTailBound := by
  intro T d j hj h Q hQ
  exact ⟨fun E => ⟨encard_regions_of_extent_le htree hpres hgraph hlat hcubes d hj h hQ E,
    treeCountBound_eq E⟩, fun κ' D hκ _ => tail_sum_le htree hpres hgraph hlat hcubes d hj h hQ hκ⟩
end TorusBound.RegionsThroughCube
end
end YangMills.Construction
