import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.StandardPartitionCubeGeometry
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequality
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.SeparatedClasses.BlockStructureProof
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem continuous_torusProj (S : ℝ) : Continuous (torusProj S) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
section Cubes
variable {L m : ℕ}
structure LatticeHyp (L m : ℕ) : Prop where
  odd : Odd L
  ge_thirteen : 13 ≤ L
  pos : 0 < m
  geometry : StandardPartitionCubeGeometry
theorem LatticeHyp.supFacts (G : LatticeHyp L m) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    CubeSupDistanceFacts L m i :=
  (G.geometry L m G.odd G.ge_thirteen G.pos i hi).2.1
theorem LatticeHyp.refinement (G : LatticeHyp L m) {i : ℤ} (hi : -(m : ℤ) ≤ i) (n : ℕ) :
    RefinementCubeFacts L m i n :=
  (G.geometry L m G.odd G.ge_thirteen G.pos i hi).1 n
theorem LatticeHyp.L_pos (G : LatticeHyp L m) : 0 < L := by
  have := G.ge_thirteen
  omega
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem mem_cubeAround {j : ℤ} {y : Site L m j} {x : FourTorus L m} :
    x ∈ cubeAround y ↔ ‖x - (y : FourTorus L m)‖ ≤ meshSize L j / 2 := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.mem_cubeAround <;> assumption
def openCubeAround {j : ℤ} (y : Site L m j) : Set (FourTorus L m) :=
  {x | ‖x - (y : FourTorus L m)‖ < meshSize L j / 2}
theorem isClosed_cubeAround {j : ℤ} (y : Site L m j) : IsClosed (cubeAround y) := by apply _root_.YangMills.Construction.SeparatedSequence.isClosed_cubeAround <;> assumption
theorem openCubeAround_subset {j : ℤ} (y : Site L m j) : openCubeAround y ⊆ cubeAround y :=
  fun _ hx => mem_cubeAround.2 (le_of_lt hx)
theorem centre_mem_openCubeAround (hL : 0 < L) {j : ℤ} (y : Site L m j) :
    (y : FourTorus L m) ∈ openCubeAround y := by
  simp only [openCubeAround, mem_setOf_eq, sub_self, norm_zero]
  have := meshSize_pos hL j
  linarith
theorem cubeAround_subset_closure (hL : 0 < L) {j : ℤ} (y : Site L m j) :
    cubeAround y ⊆ closure (openCubeAround y) := by
  intro x hx
  have hx' := mem_cubeAround.1 hx
  have ha := meshSize_pos hL j
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm ((x - (y : FourTorus L m)) μ)
  have hcov : torusProj (torusSide L m) b = x - (y : FourTorus L m) := funext hb
  let f : ℝ → FourTorus L m := fun s => (y : FourTorus L m) + torusProj (torusSide L m) (s • b)
  have hf : Continuous f :=
    continuous_const.add ((continuous_torusProj _).comp (continuous_id.smul continuous_const))
  have h1 : f 1 = x := by
    simp only [f, one_smul, hcov]
    abel
  have hmaps : MapsTo f (Ico 0 1) (openCubeAround y) := by
    rintro s ⟨hs0, hs1⟩
    simp only [openCubeAround, mem_setOf_eq, f, add_sub_cancel_left]
    refine (pi_norm_lt_iff (by linarith)).2 fun μ => ?_
    refine (addCircle_norm_coe_le_abs _).trans_lt ?_
    have h2 : ‖(x - (y : FourTorus L m)) μ‖ ≤ meshSize L j / 2 :=
      (norm_le_pi_norm (x - (y : FourTorus L m)) μ).trans hx'
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hs0, hb' μ]
    nlinarith [norm_nonneg ((x - (y : FourTorus L m)) μ)]
  have hc : (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) := by
    rw [closure_Ico (by norm_num)]
    exact ⟨by norm_num, le_rfl⟩
  have := map_mem_closure hf hc hmaps
  rwa [h1] at this
theorem eq_cubeAround_of_mem_open (G : LatticeHyp L m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {y : Site L m i} {x : FourTorus L m} (hx : x ∈ openCubeAround y) {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m i) (hxQ : x ∈ Q) : Q = cubeAround y :=
  (G.supFacts hi).2.2.2.2.2.1 y x (by rw [torusSupNorm_eq_norm]; exact hx) Q hQ hxQ
theorem eq_of_mem_interior_of_mem (G : LatticeHyp L m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {Q Q' : Set (FourTorus L m)} (hQ : Q ∈ standardCubePartition L m i)
    (hQ' : Q' ∈ standardCubePartition L m i) {p : FourTorus L m} (hp : p ∈ interior Q)
    (hp' : p ∈ Q') : Q = Q' := by
  obtain ⟨y', rfl⟩ := hQ'
  obtain ⟨x, hxI, hxO⟩ :=
    mem_closure_iff.1 (cubeAround_subset_closure G.L_pos y' hp') _ isOpen_interior hp
  exact eq_cubeAround_of_mem_open G hi hxO hQ (interior_subset hxI)
theorem isClosed_of_mem_standardCubePartition {j : ℤ} {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m j) : IsClosed Q := by
  obtain ⟨z, rfl⟩ := hQ
  exact isClosed_cubeAround z
theorem isPartitionRegion_empty (i : ℤ) : IsPartitionRegion (L := L) (m := m) i ∅ :=
  ⟨∅, empty_subset _, sUnion_empty.symm⟩
theorem exists_cube_subset_of_mem {i : ℤ} {X : Set (FourTorus L m)}
    (hX : IsPartitionRegion i X) {p : FourTorus L m} (hp : p ∈ X) :
    ∃ Q ∈ standardCubePartition L m i, Q ⊆ X ∧ p ∈ Q := by
  obtain ⟨C, hC, rfl⟩ := hX
  obtain ⟨Q, hQ, hpQ⟩ := hp
  exact ⟨Q, hC hQ, subset_sUnion_of_mem hQ, hpQ⟩
theorem isClosed_sUnion_of_subset (hL : 0 < L) {i : ℤ} {C : Set (Set (FourTorus L m))}
    (hC : C ⊆ standardCubePartition L m i) : IsClosed (⋃₀ C) := by
  have := SeparatedSequences.BaseParameters.site_finite hL m i
  rw [sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion ((finite_range _).subset hC)
    fun Q hQ => isClosed_of_mem_standardCubePartition (hC hQ)
theorem isClosed_of_isPartitionRegion (hL : 0 < L) {i : ℤ} {X : Set (FourTorus L m)}
    (hX : IsPartitionRegion i X) : IsClosed X := by
  obtain ⟨C, hC, rfl⟩ := hX
  exact isClosed_sUnion_of_subset hL hC
theorem closure_diff_eq_sUnion (G : LatticeHyp L m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {X Y : Set (FourTorus L m)} (hX : IsPartitionRegion i X) (hY : IsPartitionRegion i Y) :
    closure (X \ Y) = ⋃₀ {Q | Q ∈ standardCubePartition L m i ∧ Q ⊆ X ∧ ¬Q ⊆ Y} := by
  apply Subset.antisymm
  · refine closure_minimal ?_ (isClosed_sUnion_of_subset G.L_pos fun Q hQ => hQ.1)
    rintro p ⟨hpX, hpY⟩
    obtain ⟨Q, hQ, hQX, hpQ⟩ := exists_cube_subset_of_mem hX hpX
    exact ⟨Q, ⟨hQ, hQX, fun h => hpY (h hpQ)⟩, hpQ⟩
  · rintro p ⟨Q, ⟨⟨y, rfl⟩, hQX, hQY⟩, hpQ⟩
    refine closure_mono ?_ (cubeAround_subset_closure G.L_pos y hpQ)
    intro x hx
    refine ⟨hQX (openCubeAround_subset y hx), fun hxY => hQY ?_⟩
    obtain ⟨Q', hQ', hQ'Y, hxQ'⟩ := exists_cube_subset_of_mem hY hxY
    rw [← eq_cubeAround_of_mem_open G hi hx hQ' hxQ']
    exact hQ'Y
end Cubes
section Sequence
variable (C : ClassData)
theorem neg_m_le_levelDepth {n : ℕ} (hn : n ≤ C.t) : -(C.m : ℤ) ≤ levelDepth C.cutoff n := by
  have := C.t_le_cutoff
  have h1 : (n : ℤ) ≤ (C.cutoff : ℤ) := by exact_mod_cast hn.trans this
  have h2 : (0 : ℤ) ≤ (C.m : ℤ) := by positivity
  simp only [levelDepth]
  omega
variable {C} {Ω : ℕ → Set C.Point}
theorem memberAt_eq (hΩ : Ω ∈ C.separatedClass) (n : ℕ) : C.memberAt Ω n = Ω n := by
  simp only [ClassData.memberAt, SeparatedSequences.truncatedMember]
  split_ifs with h
  · rfl
  · exact (hΩ.2.2 n (not_le.1 h)).symm
theorem isPartitionRegion_apply (G : LatticeHyp C.L C.m) (hΩ : Ω ∈ C.separatedClass) {i n : ℕ}
    (hin : i ≤ n) : IsPartitionRegion (levelDepth C.cutoff i) (Ω n) := by
  by_cases hn : n ≤ C.t
  · rcases hΩ.2.1.1 n hn with h0 | ⟨hm, hr⟩
    · rw [h0]
      exact isPartitionRegion_empty _
    · have h1 := (G.refinement hm (n - i + C.blockExp)).2.2.2.1 _ hr
      have hidx : C.scales.blockPartitionIndex n + ((n - i + C.blockExp : ℕ) : ℤ) =
          levelDepth C.cutoff i := by
        change (((C.K : ℕ) : ℤ) - (n : ℤ) - (C.blockExp : ℤ)) +
          ((n - i + C.blockExp : ℕ) : ℤ) = ((C.K : ℕ) : ℤ) - (i : ℤ)
        omega
      rwa [hidx] at h1
  · rw [hΩ.2.2 n (by omega)]
    exact isPartitionRegion_empty _
def layerCubeSet (Ω : ℕ → Set C.Point) (n : ℕ) : Set (Set C.Point) :=
  {Q | Q ∈ standardCubePartition C.L C.m (levelDepth C.cutoff n) ∧ Q ⊆ Ω n ∧ ¬Q ⊆ Ω (n + 1)}
theorem layerAt_eq_closure (G : LatticeHyp C.L C.m) (hΩ : Ω ∈ C.separatedClass) {n : ℕ}
    (hn : n ≤ C.t) : C.layerAt Ω n = closure (Ω n \ Ω (n + 1)) := by
  simp only [ClassData.layerAt, SeparatedSequences.layerSet]
  rcases hn.lt_or_eq with h | h
  · rw [if_pos h]
  · subst h
    rw [if_neg (lt_irrefl _), if_pos rfl, hΩ.2.2 (C.scales.top + 1) (Nat.lt_succ_self _),
      diff_empty,
      (isClosed_of_isPartitionRegion G.L_pos
        (isPartitionRegion_apply G hΩ (le_refl C.scales.top))).closure_eq]
theorem layerAt_eq_sUnion (G : LatticeHyp C.L C.m) (hΩ : Ω ∈ C.separatedClass) {n : ℕ}
    (hn : n ≤ C.t) : C.layerAt Ω n = ⋃₀ layerCubeSet Ω n := by
  rw [layerAt_eq_closure G hΩ hn]
  exact closure_diff_eq_sUnion G (neg_m_le_levelDepth C hn) (isPartitionRegion_apply G hΩ le_rfl)
    (isPartitionRegion_apply G hΩ (Nat.le_succ n))
theorem diff_subset_layerAt (G : LatticeHyp C.L C.m) (hΩ : Ω ∈ C.separatedClass) {n : ℕ}
    (hn : n ≤ C.t) : Ω n \ Ω (n + 1) ⊆ C.layerAt Ω n := by
  rw [layerAt_eq_closure G hΩ hn]
  exact subset_closure
theorem mem_layerSitesAt_iff_cube (G : LatticeHyp C.L C.m) (hΩ : Ω ∈ C.separatedClass) {n : ℕ}
    (hn : n ≤ C.t) (y : C.LatticeSite n) :
    y ∈ C.layerSitesAt Ω n ↔ cubeAround y ∈ layerCubeSet Ω n := by
  constructor
  · intro hy
    have hy' : (y : C.Point) ∈ C.layerAt Ω n := hy
    rw [layerAt_eq_sUnion G hΩ hn] at hy'
    obtain ⟨Q, hQ, hyQ⟩ := hy'
    rw [← eq_cubeAround_of_mem_open G (neg_m_le_levelDepth C hn)
      (centre_mem_openCubeAround G.L_pos y) hQ.1 hyQ]
    exact hQ
  · intro hy
    have : (y : C.Point) ∈ C.layerAt Ω n := by
      rw [layerAt_eq_sUnion G hΩ hn]
      exact ⟨_, hy, openCubeAround_subset y (centre_mem_openCubeAround G.L_pos y)⟩
    exact this
theorem mem_layerSitesAt_iff (G : LatticeHyp C.L C.m) (hΩ : Ω ∈ C.separatedClass) {n : ℕ}
    (hn : n ≤ C.t) (y : C.LatticeSite n) :
    y ∈ C.layerSitesAt Ω n ↔ (y : C.Point) ∈ Ω n ∧ (y : C.Point) ∉ Ω (n + 1) := by
  have hc := centre_mem_openCubeAround G.L_pos y
  constructor
  · intro hy
    have hq := (mem_layerSitesAt_iff_cube G hΩ hn y).1 hy
    refine ⟨hq.2.1 (openCubeAround_subset y hc), fun hy' => hq.2.2 ?_⟩
    obtain ⟨Q, hQ, hQY, hyQ⟩ :=
      exists_cube_subset_of_mem (isPartitionRegion_apply G hΩ (Nat.le_succ n)) hy'
    rw [← eq_cubeAround_of_mem_open G (neg_m_le_levelDepth C hn) hc hQ hyQ]
    exact hQY
  · intro hy
    exact diff_subset_layerAt G hΩ hn hy
theorem disjoint_interior_succ (G : LatticeHyp C.L C.m) (hΩ : Ω ∈ C.separatedClass) {n : ℕ}
    (hn : n ≤ C.t) {y : C.LatticeSite n} (hy : y ∈ C.layerSitesAt Ω n) :
    Disjoint (interior (cubeAround y)) (Ω (n + 1)) := by
  have hq := (mem_layerSitesAt_iff_cube G hΩ hn y).1 hy
  refine disjoint_left.2 fun x hx hx' => hq.2.2 ?_
  obtain ⟨Q, hQ, hQY, hxQ⟩ :=
    exists_cube_subset_of_mem (isPartitionRegion_apply G hΩ (Nat.le_succ n)) hx'
  rw [eq_of_mem_interior_of_mem G (neg_m_le_levelDepth C hn) hq.1 hQ hx hxQ]
  exact hQY
theorem exists_site_of_mem_layerAt (G : LatticeHyp C.L C.m) (hΩ : Ω ∈ C.separatedClass) {n : ℕ}
    (hn : n ≤ C.t) {p : C.Point} (hp : p ∈ C.layerAt Ω n) :
    ∃ y ∈ C.layerSitesAt Ω n, p ∈ cubeAround y := by
  rw [layerAt_eq_sUnion G hΩ hn] at hp
  obtain ⟨Q, hQ, hpQ⟩ := hp
  obtain ⟨y, rfl⟩ := hQ.1
  exact ⟨y, (mem_layerSitesAt_iff_cube G hΩ hn y).2 hQ, hpQ⟩
end Sequence
section Apexes
variable {C : ClassData} {Ω : ℕ → Set C.Point}
theorem exists_level_mem_not_mem_succ (hΩ : Ω ∈ C.separatedClass) {p : C.Point} (hp : p ∈ Ω 0) :
    ∃ n ≤ C.t, p ∈ Ω n ∧ p ∉ Ω (n + 1) := by
  classical
  have hex : ∃ n, p ∉ Ω (n + 1) :=
    ⟨C.t, by rw [hΩ.2.2 (C.t + 1) (Nat.lt_succ_self _)]; simp⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · refine Nat.find_min' hex ?_
    rw [hΩ.2.2 (C.t + 1) (Nat.lt_succ_self _)]
    simp
  · rcases hk : Nat.find hex with _ | k
    · exact hp
    · have := Nat.find_min hex (m := k) (by omega)
      exact not_not.1 this
theorem exists_apex (G : LatticeHyp C.L C.m) (hΩ : Ω ∈ C.separatedClass) {p : C.Point}
    (hp : p ∈ Ω 0) : ∃ y : C.Apex Ω, p ∈ y.block := by
  obtain ⟨n, hn, h1, h2⟩ := exists_level_mem_not_mem_succ hΩ hp
  obtain ⟨y, hy, hpy⟩ :=
    exists_site_of_mem_layerAt G hΩ hn (diff_subset_layerAt G hΩ hn ⟨h1, h2⟩)
  exact ⟨⟨⟨n, y⟩, hn, hy⟩, hpy⟩
end Apexes
section SeriesExpansions
variable {C : ClassData} {Ω : ℕ → Set C.Point}
def forwardBond {L m : ℕ} {j : ℤ} (x : Site L m j) (μ : Fin 4) :
    PositivelyOrientedBond L m j :=
  ⟨Bond.forwardFrom x μ, μ, add_sub_cancel_left _ _⟩
end SeriesExpansions
section Triangle
variable {C : ClassData}
theorem segmentsSupport_append (S : ℝ) (Γ Γ' : List LiftedSegment) :
    segmentsSupport S (Γ ++ Γ') = segmentsSupport S Γ ∪ segmentsSupport S Γ' := by
  ext p
  simp only [segmentsSupport, mem_iUnion, mem_union, List.mem_append, exists_prop]
  constructor
  · rintro ⟨s, hs | hs, hp⟩
    · exact Or.inl ⟨s, hs, hp⟩
    · exact Or.inr ⟨s, hs, hp⟩
  · rintro (⟨s, hs, hp⟩ | ⟨s, hs, hp⟩)
    · exact ⟨s, Or.inl hs, hp⟩
    · exact ⟨s, Or.inr hs, hp⟩
theorem pathLengthIn_append (S : ℝ) (Γ Γ' : List LiftedSegment) (A : Set (Torus4 S)) :
    pathLengthIn S (Γ ++ Γ') A = pathLengthIn S Γ A + pathLengthIn S Γ' A := by
  simp only [pathLengthIn, List.map_append, List.sum_append]
theorem chainLength_append (Ω : ℕ → Set C.Point) (Γ Γ' : List LiftedSegment) :
    C.chainLength Ω (Γ ++ Γ') = C.chainLength Ω Γ + C.chainLength Ω Γ' := by
  simp only [ClassData.chainLength, SeparatedSequences.layerWeightedLength, pathLengthIn_append,
    SeparatedSequences.ScaleData.toUnits, PeriodicLattice.toLevelUnits, mul_add,
    Finset.sum_add_distrib]
  ring
end Triangle
end YangMills.Construction.SeparatedClasses.BlockStructureProof
end
