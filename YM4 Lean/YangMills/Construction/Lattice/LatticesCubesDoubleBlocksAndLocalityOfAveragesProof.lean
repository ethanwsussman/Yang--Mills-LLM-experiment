import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.BondwiseAveragesAreTheBlockAverages
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Lattice.DoubleBlockFromItsLowestCornerProof
import YangMills.Construction.Lattice.LatticesCubesDoubleBlocksAndLocalityOfAverages
import YangMills.Construction.Lattice.LocalityAndGaugeCovarianceOfTheAveragingMap
import YangMills.Construction.Lattice.StandardPartitionCubeGeometry
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace PeriodicLattice.GeometryAndLocalityOfBlockAverages
variable {L m K : ℕ}
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem meshSize_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℤ) :
    0 < meshSize L j := by
  have : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
  exact zpow_pos this _
theorem meshSize_add_mul_pow (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℤ) (n : ℕ) :
    meshSize L (j + n) * (L : ℝ) ^ n = meshSize L j := by
  have h : (L : ℝ) ≠ 0 := by exact_mod_cast (by have := hL.2; omega : L ≠ 0)
  simp only [meshSize]
  rw [← zpow_natCast, ← zpow_add₀ h]
  congr 1
  ring
theorem toBareUnits_eq (r : ℝ) : toBareUnits L K r = (L : ℝ) ^ K * r := by
  simp [toBareUnits, toLevelUnits, levelDepth]
theorem pow_eq_mul_meshSize_levelDepth (hL : Conventions.IsAdmissibleBlockingFactor L) (q : ℕ) :
    (L : ℝ) ^ q = (L : ℝ) ^ K * meshSize L (levelDepth K q) := by
  have h : (L : ℝ) ≠ 0 := by exact_mod_cast (by have := hL.2; omega : L ≠ 0)
  simp only [meshSize, levelDepth]
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h]
  congr 1
  ring
theorem blockingFactor_pow_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (n : ℕ) :
    (0 : ℝ) < (L : ℝ) ^ n := by
  have : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
  positivity
theorem self_mem_cubeAround (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℤ}
    (y : Site L m j) : (y : FourTorus L m) ∈ cubeAround y := by
  show _root_.YangMills.Construction.TorusMetric.torusSupNorm _ ≤ _
  rw [sub_self, _root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.torusSupNorm_eq_norm, norm_zero]
  exact (half_pos (meshSize_pos hL j)).le
theorem norm_sub_le_of_mem_refinedBlock (hC : StandardPartitionCubeGeometry)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℤ} (hj : -(m : ℤ) ≤ j)
    (n : ℕ) (y : Site L m j) {x : FourTorus L m} (hx : x ∈ refinedBlock n y) :
    ‖x - (y : FourTorus L m)‖ ≤ (meshSize L j - meshSize L (j + n)) / 2 := by
  have hblk := ((hC L m hL.1 hL.2 hm j hj).1 n).1 y
  rw [hblk] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hs := meshSize_pos hL (j + n)
  have hmul := meshSize_add_mul_pow hL j n
  have hnonneg : 0 ≤ (meshSize L j - meshSize L (j + n)) / 2 := by
    have hpow : (1 : ℝ) ≤ (L : ℝ) ^ n :=
      one_le_pow₀ (by exact_mod_cast (by have := hL.2; omega : 1 ≤ L))
    nlinarith
  rw [add_sub_cancel_left]
  refine (pi_norm_le_iff_of_nonneg hnonneg).2 fun μ => ?_
  refine (addCircle_norm_coe_le_abs _).trans ?_
  rw [abs_mul, abs_of_pos hs]
  have := hp μ
  calc meshSize L (j + n) * |(p μ : ℝ)| ≤ meshSize L (j + n) * (((L : ℝ) ^ n - 1) / 2) :=
        mul_le_mul_of_nonneg_left this hs.le
    _ = (meshSize L j - meshSize L (j + n)) / 2 := by rw [← hmul]; ring
theorem torusSupNorm_sub_lt_of_mem_refinedBlock (hC : StandardPartitionCubeGeometry)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℤ} (hj : -(m : ℤ) ≤ j)
    (n : ℕ) (y : Site L m j) {x : FourTorus L m} (hx : x ∈ refinedBlock n y) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - (y : FourTorus L m)) < meshSize L j / 2 := by
  rw [_root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.torusSupNorm_eq_norm]
  have := norm_sub_le_of_mem_refinedBlock hC hL hm hj n y hx
  have := meshSize_pos hL (j + n)
  linarith
theorem sublatticesAndCubesInBareUnits (hC : StandardPartitionCubeGeometry)
    (hU : CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) :
    SublatticesAndCubesInBareUnits L m K := by
  have hLpos : 0 < L := by have := hL.2; omega
  refine ⟨?_, fun q hq => ⟨?_, ?_, ?_, fun i hi => ?_⟩, fun q hq => ⟨?_, ?_, ?_⟩⟩
  · rw [toBareUnits_eq, torusSide, pow_add]
    ring
  · rw [toBareUnits_eq, ← pow_eq_mul_meshSize_levelDepth hL]
  · intro y μ
    exact ((hU L m hL.1 hL.2 hm).2.1 K q hK hq).2.1 y μ
  · have : L ≤ L ^ (m + K - q) := Nat.le_self_pow (by omega) L
    omega
  · exact sublattice_mono hLpos m (by simp only [levelDepth]; omega)
  · simp only [levelDepth]
    omega
  · intro y
    ext x
    have h := pow_eq_mul_meshSize_levelDepth (K := K) hL q
    have hp := blockingFactor_pow_pos hL K
    show _root_.YangMills.Construction.TorusMetric.torusSupNorm _ ≤ _ ↔ _
    rw [mem_ofPred_eq, toBareUnits_eq, h, mul_div_assoc]
    exact (mul_le_mul_iff_right₀ hp).symm
  · exact (hC L m hL.1 hL.2 hm (levelDepth K q)
      (by simp only [levelDepth]; omega)).2.1.2.2.2.2.1
theorem sitesInPartitionCubes (hC : StandardPartitionCubeGeometry)
    (hB : BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i q : ℕ} (hiq : i ≤ q)
    (hq : q ≤ K + 1) : SitesInPartitionCubes L m K i q := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n, q = i + n := ⟨q - i, by omega⟩
  have hj : -(m : ℤ) ≤ levelDepth K (i + n) := by
    simp only [levelDepth]; push_cast at hq ⊢; omega
  have e : levelDepth K (i + n) + (n : ℤ) = levelDepth K i := by
    simp only [levelDepth]; push_cast; ring
  have hxl : (x : FourTorus L m) ∈ sublattice L m (levelDepth K (i + n) + n) := by
    rw [e]; exact x.2
  have hS := (hC L m hL.1 hL.2 hm (levelDepth K (i + n)) hj).2.1
  have near : ∀ y : SiteAtLevel L m K (i + n), (x : FourTorus L m) ∈ cubeAround y →
      ‖(x : FourTorus L m) - (y : FourTorus L m)‖ ≤
        (meshSize L (levelDepth K (i + n)) - meshSize L (levelDepth K i)) / 2 := fun y hy => by
    have := norm_sub_le_of_mem_refinedBlock hC hL hm hj n y (x := x) ⟨hy, hxl⟩
    rwa [e] at this
  have hsi := meshSize_pos hL (levelDepth K i)
  have nearlt : ∀ y : SiteAtLevel L m K (i + n), (x : FourTorus L m) ∈ cubeAround y →
      _root_.YangMills.Construction.TorusMetric.torusSupNorm ((x : FourTorus L m) - (y : FourTorus L m)) <
        meshSize L (levelDepth K (i + n)) / 2 :=
    fun y hy => by
      rw [_root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.torusSupNorm_eq_norm]
      have := near y hy
      linarith
  have hP := (hB L m hL hm (levelDepth K (i + n)) n 0 hj).2.1
  have hcover : (x : FourTorus L m) ∈
      ⋃ y : Site L m (levelDepth K (i + n)), refinedBlock n y := by
    rw [hP.2.2.2]
    exact hxl
  obtain ⟨y₀, hy₀⟩ := mem_iUnion.1 hcover
  have uniq : ∀ y : SiteAtLevel L m K (i + n), (x : FourTorus L m) ∈ cubeAround y →
      ∀ Q ∈ cubePartitionOfSide L m K (i + n), (x : FourTorus L m) ∈ Q → Q = cubeAround y :=
    fun y hy Q hQ hxQ => hS.2.2.2.2.2.1 y x (nearlt y hy) Q hQ hxQ
  refine ⟨⟨cubeAround y₀, ⟨⟨y₀, rfl⟩, hy₀.1⟩, fun Q hQ => uniq y₀ hy₀.1 Q hQ.1 hQ.2⟩, ?_, ?_⟩
  · intro y hy
    rw [toBareUnits_eq, pow_eq_mul_meshSize_levelDepth (K := K) hL (i + n), mul_div_assoc]
    exact mul_lt_mul_of_pos_left (nearlt y hy) (blockingFactor_pow_pos hL K)
  · intro X hX Q hQ hxQ
    obtain ⟨y, rfl⟩ := hQ
    have key : (x : FourTorus L m) ∈ X ↔
        cubeAround y ∈ partitionCubesIn (levelDepth K (i + n)) X := by
      refine ⟨fun hxX => ?_, fun h => h.2 hxQ⟩
      obtain ⟨C, hCs, rfl⟩ := hX
      obtain ⟨Q', hQ'C, hxQ'⟩ := hxX
      have := uniq y hxQ Q' (hCs hQ'C) hxQ'
      subst this
      exact ⟨⟨y, rfl⟩, subset_sUnion_of_mem hQ'C⟩
    refine ⟨key, fun hxX z hz => (key.1 hxX).2 ?_⟩
    have h1 : ‖z - (x : FourTorus L m)‖ < meshSize L (levelDepth K i) / 2 := by
      rw [mem_ofPred_eq, toBareUnits_eq, pow_eq_mul_meshSize_levelDepth (K := K) hL i,
        mul_div_assoc, _root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.torusSupNorm_eq_norm] at hz
      exact lt_of_mul_lt_mul_left hz (blockingFactor_pow_pos hL K).le
    have h2 := near y hxQ
    show _root_.YangMills.Construction.TorusMetric.torusSupNorm _ ≤ _
    rw [_root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.torusSupNorm_eq_norm]
    calc ‖z - (y : FourTorus L m)‖ =
          ‖(z - (x : FourTorus L m)) + ((x : FourTorus L m) - y)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖z - (x : FourTorus L m)‖ + ‖(x : FourTorus L m) - y‖ := norm_add_le _ _
      _ ≤ meshSize L (levelDepth K (i + n)) / 2 := by linarith
theorem regionsOfNestedPartitions (hT : CubesUnderRefinement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) :
    RegionsOfNestedPartitions L m K := by
  intro i q hiq hq X hX
  have ht := (hT L m hL.1 hL.2 hm).1 (levelDepth K q) (levelDepth K i)
    (by simp only [levelDepth]; omega) (by simp only [levelDepth]; omega)
  exact ⟨ht.2.2.1 X hX, ht.2.2.2 X hX⟩
theorem complementRegionIndependentOfScale (hC : StandardPartitionCubeGeometry)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) :
    ComplementRegionIndependentOfScale L m := by
  intro t t' ht htt' X hX
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, t' = t + n := ⟨(t' - t).toNat, by omega⟩
  have hR := (hC L m hL.1 hL.2 hm t ht).1 n
  have hS := (hC L m hL.1 hL.2 hm t ht).2.1
  apply Subset.antisymm
  · rintro z ⟨Q, ⟨⟨y, rfl⟩, hQ⟩, hz⟩
    rw [hR.2.1 y] at hz
    simp only [mem_iUnion] at hz
    obtain ⟨y', hy', hz'⟩ := hz
    refine ⟨cubeAround y', ⟨⟨y', rfl⟩, fun hsub => hQ ?_⟩, hz'⟩
    have hyX : (y' : FourTorus L m) ∈ X := hsub.2 (self_mem_cubeAround hL y')
    obtain ⟨C, hCs, rfl⟩ := hX
    obtain ⟨Q', hQ'C, hyQ'⟩ := hyX
    have := hS.2.2.2.2.2.1 y y'
      (_root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.torusSupNorm_sub_lt_of_mem_refinedBlock hC hL hm ht n y hy') Q' (hCs hQ'C) hyQ'
    subst this
    exact ⟨⟨y, rfl⟩, subset_sUnion_of_mem hQ'C⟩
  · rintro z ⟨Q', ⟨hQ'P, hQ'⟩, hz⟩
    obtain ⟨Q, hQP, hsub⟩ := hR.2.2.1 Q' hQ'P
    exact ⟨Q, ⟨hQP, fun h => hQ' ⟨hQ'P, hsub.trans h.2⟩⟩, hsub hz⟩
theorem sitesOfRegionDifference (hC : StandardPartitionCubeGeometry)
    (hB : BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hi : i ≤ K) :
    SitesOfRegionDifference L m K i := by
  intro X X' hX hX' x
  have hj : -(m : ℤ) ≤ levelDepth K i := by simp only [levelDepth]; omega
  obtain ⟨-, -, h3⟩ := sitesInPartitionCubes (K := K) hC hB hL hm (le_refl i) (by omega) x
  have hxQ : (x : FourTorus L m) ∈ cubeAround x := self_mem_cubeAround hL x
  have hQ : cubeAround x ∈ cubePartitionOfSide L m K i := ⟨x, rfl⟩
  refine ⟨⟨fun h => subset_closure h, fun hcl => ?_⟩, ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨z, ⟨hzX, hzX'⟩, hd⟩ :=
      Metric.mem_closure_iff.1 hcl (meshSize L (levelDepth K i) / 2)
        (half_pos (meshSize_pos hL _))
    have hzn : _root_.YangMills.Construction.TorusMetric.torusSupNorm (z - (x : FourTorus L m)) < meshSize L (levelDepth K i) / 2 := by
      rw [_root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.torusSupNorm_eq_norm, ← dist_eq_norm, dist_comm]
      exact hd
    constructor
    · obtain ⟨C, hCs, hXC⟩ := hX
      rw [hXC] at hzX ⊢
      obtain ⟨Q', hQ'C, hzQ'⟩ := hzX
      have := (hC L m hL.1 hL.2 hm _ hj).2.1.2.2.2.2.2.1 x z hzn Q' (hCs hQ'C) hzQ'
      subst this
      exact ⟨_, hQ'C, hxQ⟩
    · intro hxX'
      refine hzX' ((h3 X' hX' _ hQ hxQ).2 hxX' ?_)
      rw [mem_ofPred_eq, toBareUnits_eq, pow_eq_mul_meshSize_levelDepth (K := K) hL i,
        mul_div_assoc]
      exact mul_lt_mul_of_pos_left hzn (blockingFactor_pow_pos hL K)
  · exact ⟨_, hQ, hxQ, (h3 X hX _ hQ hxQ).1.1 h.1, fun h' => h.2 ((h3 X' hX' _ hQ hxQ).1.2 h')⟩
  · rintro ⟨Q, hQ', hxQ', h1, h2⟩
    exact ⟨(h3 X hX Q hQ' hxQ').1.2 h1, fun h' => h2 ((h3 X' hX' Q hQ' hxQ').1.1 h')⟩
theorem sitesIn_siteImage {j : ℤ} (P : Set (Site L m j)) :
    (sitesIn (sitesAsTorusPoints P) : Set (Site L m j)) = P := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlockCorner.sitesIn_siteImage <;> assumption
theorem one_le_blockingFactor_pow (hL : Conventions.IsAdmissibleBlockingFactor L) (n : ℕ) :
    (1 : ℤ) ≤ (L : ℤ) ^ n :=
  one_le_pow₀ (by exact_mod_cast (by have := hL.2; omega : 1 ≤ L))
theorem blocksAtLevelAreSiteBoxes (hBox : CornerBoxProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) {i q : ℕ}
    (hiq : i ≤ q) (hq : q ≤ K) : BlocksAtLevelAreSiteBoxes L m K i q := by
  intro y
  obtain ⟨⟨hblk, hc1, hc2⟩, -⟩ := (hBox L m K hL hm hK i (hiq.trans hq)).2 q hiq hq y
  have hN : ∀ μ, (1 : ℤ) ≤ uniformCounts ((L : ℤ) ^ (q - i)) μ ∧
      uniformCounts ((L : ℤ) ^ (q - i)) μ < (L : ℤ) ^ (m + K - i) :=
    fun μ => ⟨one_le_blockingFactor_pow hL _, lt_of_le_of_lt (hc1 μ) hc2⟩
  have hbox := (hBox L m K hL hm hK i (hiq.trans hq)).1
    (blockCorner (j' := levelDepth K i) ((L : ℤ) ^ (q - i)) y) _ hN
  show IsSiteBox _ (sitesIn (refinedBlock (q - i) y))
  rw [hblk, sitesIn_siteImage]
  exact hbox.1
theorem bond_target_sub_source {j : ℤ} (c : Bond L m j) :
    c.target - c.source = unitStep L m j c.axis ∨
      c.target - c.source = -unitStep L m j c.axis :=
  c.isNeighbour.choose_spec
theorem exists_forwardFrom_bareBlockPair {q : ℕ} (c : BondAtLevel L m K q) :
    ∃ y : SiteAtLevel L m K q,
      bareBlockPair c = refinedBlock (q - 0) (Bond.forwardFrom y c.axis).source ∪
        refinedBlock (q - 0) (Bond.forwardFrom y c.axis).target := by
  rcases bond_target_sub_source c with h | h
  · refine ⟨c.source, ?_⟩
    have e : c.source + unitStep L m (levelDepth K q) c.axis = c.target := by rw [← h]; abel
    simp only [Bond.forwardFrom]
    rw [e]
    rfl
  · refine ⟨c.target, ?_⟩
    have e : c.target + unitStep L m (levelDepth K q) c.axis = c.source := by
      rw [← neg_eq_iff_eq_neg.mpr h]; abel
    simp only [Bond.forwardFrom]
    rw [e, union_comm]
    rfl
theorem bareBlockPair_isSiteBox (hBox : CornerBoxProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) {q : ℕ}
    (hq : q ≤ K) (c : BondAtLevel L m K q) :
    IsSiteBox (levelDepth K 0) (sitesIn (bareBlockPair c) : Set (SiteAtLevel L m K 0)) ∧
    HasSiteCounts (levelDepth K 0) (sitesIn (bareBlockPair c) : Set (SiteAtLevel L m K 0))
      (doubledCounts ((L : ℤ) ^ q) c.axis) := by
  obtain ⟨y, hy⟩ := exists_forwardFrom_bareBlockPair c
  obtain ⟨-, hfw, -⟩ := (hBox L m K hL hm hK 0 (Nat.zero_le K)).2 q (Nat.zero_le q) hq y
  obtain ⟨hblk, hc1, hc2⟩ := hfw c.axis
  have hN : ∀ ν, (1 : ℤ) ≤ doubledCounts ((L : ℤ) ^ (q - 0)) c.axis ν ∧
      doubledCounts ((L : ℤ) ^ (q - 0)) c.axis ν < (L : ℤ) ^ (m + K - 0) := by
    intro ν
    refine ⟨?_, lt_of_le_of_lt (hc1 ν) hc2⟩
    have h1 := one_le_blockingFactor_pow hL (q - 0)
    by_cases h : ν = c.axis
    · subst h
      simp only [doubledCounts, Function.update_self]
      omega
    · simpa only [doubledCounts, Function.update_of_ne h, uniformCounts] using h1
  have hbox := (hBox L m K hL hm hK 0 (Nat.zero_le K)).1
    (blockCorner (j' := levelDepth K 0) ((L : ℤ) ^ (q - 0)) y) _ hN
  rw [hy.trans hblk, sitesIn_siteImage]
  exact hbox
theorem coe_toSublattice_of_le (hL : Conventions.IsAdmissibleBlockingFactor L) {j j' : ℤ}
    (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m j' => (x : FourTorus L m) = y)
    ⟨⟨y, sublattice_mono (by have := hL.2; omega) m h y.2⟩, rfl⟩
theorem meshSize_levelDepth (hL : Conventions.IsAdmissibleBlockingFactor L) (q : ℕ) :
    meshSize L (levelDepth K q) = (L : ℝ) ^ q * meshSize L (levelDepth K 0) := by
  have h := meshSize_add_mul_pow hL (levelDepth K q) q
  have e : levelDepth K q + (q : ℤ) = levelDepth K 0 := by
    simp only [levelDepth]; push_cast; ring
  rw [e] at h
  rw [← h]
  ring
theorem coe_unitStep_levelDepth (hL : Conventions.IsAdmissibleBlockingFactor L) (q : ℕ)
    (μ : Fin 4) :
    ((unitStep L m (levelDepth K q) μ : Site L m (levelDepth K q)) : FourTorus L m) =
      ((L : ℤ) ^ q) •
        ((unitStep L m (levelDepth K 0) μ : Site L m (levelDepth K 0)) : FourTorus L m) := by
  have hs : meshSize L (levelDepth K q) = ((L : ℤ) ^ q) • meshSize L (levelDepth K 0) := by
    rw [meshSize_levelDepth hL q, zsmul_eq_mul]
    push_cast
    ring
  funext ν
  by_cases h : ν = μ
  · subst h
    simp only [unitStep, pointOnAxis, Pi.smul_apply, Pi.single_eq_same]
    rw [hs, AddCircle.coe_zsmul]
  · simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem norm_unitStep_le (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℤ) (μ : Fin 4) :
    ‖((unitStep L m j μ : Site L m j) : FourTorus L m)‖ ≤ meshSize L j := by
  have hs := meshSize_pos hL j
  refine (pi_norm_le_iff_of_nonneg hs.le).2 fun ν => ?_
  by_cases h : ν = μ
  · subst h
    simp only [unitStep, pointOnAxis, Pi.single_eq_same]
    exact (addCircle_norm_coe_le_abs _).trans (abs_of_pos hs).le
  · simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h, hs.le]
theorem mem_bareBlock_of_axial (hL : Conventions.IsAdmissibleBlockingFactor L) {q : ℕ}
    (y : SiteAtLevel L m K q) (z : SiteAtLevel L m K 0) (μ : Fin 4) (k h : ℤ)
    (hh : 2 * h + 1 = (L : ℤ) ^ q) (hk : -h ≤ k ∧ k ≤ h)
    (hz : (z : FourTorus L m) - y =
      k • ((unitStep L m (levelDepth K 0) μ : Site L m (levelDepth K 0)) : FourTorus L m)) :
    (z : FourTorus L m) ∈ bareBlock y := by
  show (z : FourTorus L m) ∈ blockAtLevel 0 y
  rw [blockAtLevel_eq_cubeAtLevel_inter (Nat.zero_le q) y]
  refine ⟨?_, z.2⟩
  show _root_.YangMills.Construction.TorusMetric.torusSupNorm _ ≤ _
  rw [_root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.torusSupNorm_eq_norm, hz, meshSize_levelDepth hL q]
  have hs := meshSize_pos hL (levelDepth K 0)
  have h1 : ‖k • ((unitStep L m (levelDepth K 0) μ : Site L m (levelDepth K 0)) :
      FourTorus L m)‖ ≤ ‖k‖ * meshSize L (levelDepth K 0) :=
    (norm_zsmul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_unitStep_le hL _ μ) (norm_nonneg _))
  have h2 : ‖k‖ ≤ (h : ℝ) := by
    rw [Int.norm_eq_abs]
    have : |k| ≤ h := abs_le.2 hk
    exact_mod_cast this
  have h3 : (2 : ℝ) * h + 1 = (L : ℝ) ^ q := by exact_mod_cast hh
  have h4 := mul_le_mul_of_nonneg_right h2 hs.le
  nlinarith
theorem mem_pathSites_forwardFlow {j : ℤ} (μ : Fin 4) (t : ℕ) (x z : Site L m j)
    (hz : z ∈ sitesOfPath x (forwardAxisPath x μ t)) :
    ∃ s : ℕ, s ≤ t ∧ z = x + (s : ℤ) • unitStep L m j μ := by
  induction t generalizing x with
  | zero =>
    simp only [sitesOfPath, forwardAxisPath, List.map_nil, List.mem_singleton] at hz
    exact ⟨0, le_refl _, by simp [hz]⟩
  | succ n ih =>
    rcases List.mem_cons.1 hz with rfl | hz'
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · have hz'' : z ∈ sitesOfPath (x + unitStep L m j μ)
          (forwardAxisPath (x + unitStep L m j μ) μ n) := hz'
      obtain ⟨s, hs, rfl⟩ := ih _ hz''
      refine ⟨s + 1, by omega, ?_⟩
      push_cast
      rw [add_zsmul, one_zsmul]
      abel
theorem mem_pathSites_backwardFlow {j : ℤ} (μ : Fin 4) (t : ℕ) (x z : Site L m j)
    (hz : z ∈ sitesOfPath x (backwardAxisPath x μ t)) :
    ∃ s : ℕ, s ≤ t ∧ z = x + (-(s : ℤ)) • unitStep L m j μ := by
  induction t generalizing x with
  | zero =>
    simp only [sitesOfPath, backwardAxisPath, List.map_nil, List.mem_singleton] at hz
    exact ⟨0, le_refl _, by simp [hz]⟩
  | succ n ih =>
    rcases List.mem_cons.1 hz with rfl | hz'
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · have hz'' : z ∈ sitesOfPath (x - unitStep L m j μ)
          (backwardAxisPath (x - unitStep L m j μ) μ n) := hz'
      obtain ⟨s, hs, rfl⟩ := ih _ hz''
      refine ⟨s + 1, by omega, ?_⟩
      push_cast
      rw [neg_add, add_zsmul, neg_one_zsmul]
      abel
theorem mem_pathSites_flowAlong {j : ℤ} (μ : Fin 4) (N : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hN : 0 < N) (x z : Site L m j) (hz : z ∈ sitesOfPath x (flowAlong x μ (ε * N))) :
    ∃ s : ℕ, s ≤ N ∧ z = x + (ε * s) • unitStep L m j μ := by
  rcases hε with rfl | rfl
  · have h0 : (0 : ℤ) ≤ 1 * (N : ℤ) := by omega
    rw [flowAlong, if_pos h0] at hz
    have e : (1 * (N : ℤ)).toNat = N := by omega
    rw [e] at hz
    obtain ⟨s, hs, rfl⟩ := mem_pathSites_forwardFlow μ N x z hz
    exact ⟨s, hs, by simp⟩
  · have h0 : ¬(0 : ℤ) ≤ -1 * (N : ℤ) := by omega
    rw [flowAlong, if_neg h0] at hz
    have e : (-(-1 * (N : ℤ))).toNat = N := by omega
    rw [e] at hz
    obtain ⟨s, hs, rfl⟩ := mem_pathSites_backwardFlow μ N x z hz
    exact ⟨s, hs, by simp⟩
theorem offsetSite_single {j : ℤ} (x : Site L m j) (μ : Fin 4) (n : ℤ) :
    offsetSite x (Pi.single μ n) = x + n • unitStep L m j μ := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlockCorner.offsetSite_single <;> assumption
theorem axialPath_eq_flowAlong (hU : CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℤ} (hj : -(m : ℤ) ≤ j)
    (x x' : Site L m j) (μ : Fin 4) (n : ℤ) (h : IsAxialDisplacement x x' μ n) (hn : n ≠ 0) :
    axialPath x x' = flowAlong x μ n := by
  have hex : ∃ r : Fin 4 × ℤ, IsAxialDisplacement x x' r.1 r.2 := ⟨(μ, n), h⟩
  unfold axialPath
  rw [dif_pos hex]
  have hspec := hex.choose_spec
  generalize hex.choose = r at hspec ⊢
  obtain ⟨μ', n'⟩ := r
  obtain ⟨hd', hl'⟩ := hspec
  obtain ⟨hd, hl⟩ := h
  simp only at hd' hl' ⊢
  have hLC := (hU L m hL.1 hL.2 hm).1 j hj
  have hcoord := hLC.2.2.2.2.1 x (Pi.single μ n) (Pi.single μ' n')
  have heq : offsetSite x (Pi.single μ n) = offsetSite x (Pi.single μ' n') := by
    rw [offsetSite_single, offsetSite_single, ← hd, ← hd']
  have hmod := hcoord.1 heq μ
  have hbound : ∀ t : ℤ, ((|t| : ℤ) : ℝ) < (L : ℝ) ^ ((m : ℤ) + j) →
      |t| < (halfPeriod L m j : ℤ) := by
    intro t ht
    have e : ((m : ℤ) + j) = (((m : ℤ) + j).toNat : ℤ) := by omega
    rw [e, zpow_natCast] at ht
    have : ((|t| : ℤ) : ℝ) < ((L ^ ((m : ℤ) + j).toNat : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
      exact ht
    exact show |t| < ((L ^ ((m : ℤ) + j).toNat : ℕ) : ℤ) from by exact_mod_cast this
  have h1 := hbound n hl
  have h2 := hbound n' hl'
  by_cases e : μ' = μ
  · subst e
    simp only [Pi.single_eq_same] at hmod
    have hdvd := hmod.dvd
    have : n' - n = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
      have := abs_sub n' n
      push_cast
      omega
    have : n' = n := by omega
    rw [this]
  · exfalso
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm e)] at hmod
    have hdvd := hmod.symm.dvd
    have : n - 0 = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
      push_cast
      simp only [sub_zero]
      omega
    omega
theorem bareAxialPath_subset_bareBlockPair (hU : CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {q : ℕ} (hq : q ≤ K)
    (c : BondAtLevel L m K q) :
    (∃ (μ : Fin 4) (n : ℤ), IsAxialDisplacement (c.source.toSublattice (levelDepth K 0))
      (c.target.toSublattice (levelDepth K 0)) μ n) ∧
    ∀ z ∈ sitesOfPath (c.source.toSublattice (levelDepth K 0)) (bareAxialPath c),
      (z : FourTorus L m) ∈ bareBlockPair c := by
  have hle : levelDepth K q ≤ levelDepth K 0 := by simp only [levelDepth]; omega
  set x := c.source.toSublattice (levelDepth K 0) with hxdef
  set x' := c.target.toSublattice (levelDepth K 0) with hx'def
  have hx : (x : FourTorus L m) = c.source := coe_toSublattice_of_le hL hle _
  have hx' : (x' : FourTorus L m) = c.target := coe_toSublattice_of_le hL hle _
  set μ := c.axis with hμ
  set st := unitStep L m (levelDepth K 0) μ with hst
  have hLgt : 1 < L := by have := hL.2; omega
  obtain ⟨ε, hε, hd⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (c.target : FourTorus L m) - c.source = (ε * (L : ℤ) ^ q) • (st : FourTorus L m) := by
    rcases bond_target_sub_source c with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      have := congrArg (Subtype.val) h
      rw [AddSubgroup.coe_sub, coe_unitStep_levelDepth (K := K) hL q] at this
      rw [this, one_mul]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have := congrArg (Subtype.val) h
      rw [AddSubgroup.coe_sub, AddSubgroup.coe_neg, coe_unitStep_levelDepth (K := K) hL q] at this
      rw [this, neg_one_mul, neg_zsmul]
  set N : ℕ := L ^ q with hNdef
  have hNz : (L : ℤ) ^ q = (N : ℤ) := by rw [hNdef]; push_cast; rfl
  have hNpos : 0 < N := by rw [hNdef]; exact Nat.pow_pos (by omega)
  rw [hNz] at hd
  have hxx : x' - x = (ε * (N : ℤ)) • st := by
    apply Subtype.ext
    rw [AddSubgroup.coe_sub, AddSubgroup.coe_zsmul, hx, hx', hd]
  have hlt : (((|ε * (N : ℤ)| : ℤ)) : ℝ) < (L : ℝ) ^ ((m : ℤ) + levelDepth K 0) := by
    have habs : |ε * (N : ℤ)| = (N : ℤ) := by
      rcases hε with rfl | rfl <;> simp
    have e : ((m : ℤ) + levelDepth K 0) = ((m + K : ℕ) : ℤ) := by
      simp only [levelDepth]; push_cast; ring
    rw [habs, e, zpow_natCast, hNdef]
    push_cast
    exact pow_lt_pow_right₀ (by exact_mod_cast hLgt) (by omega)
  have haxial : IsAxialDisplacement x x' μ (ε * (N : ℤ)) := ⟨hxx, hlt⟩
  refine ⟨⟨μ, _, haxial⟩, fun z hz => ?_⟩
  have hn : ε * (N : ℤ) ≠ 0 := by
    rcases hε with rfl | rfl <;> omega
  have hj : -(m : ℤ) ≤ levelDepth K 0 := by simp only [levelDepth]; push_cast; omega
  have hpath : bareAxialPath c = flowAlong x μ (ε * (N : ℤ)) :=
    axialPath_eq_flowAlong hU hL hm hj x x' μ _ haxial hn
  rw [hpath] at hz
  obtain ⟨s, hs, rfl⟩ := mem_pathSites_flowAlong μ N ε hε hNpos x z hz
  obtain ⟨h, hh⟩ : ∃ h : ℕ, N = 2 * h + 1 := (hL.1.pow (n := q))
  have hhz : 2 * (h : ℤ) + 1 = (L : ℤ) ^ q := by rw [hNz, hh]; push_cast; ring
  have hcoe : ((x + (ε * (s : ℤ)) • st : Site L m (levelDepth K 0)) : FourTorus L m) =
      c.source + (ε * (s : ℤ)) • (st : FourTorus L m) := by
    rw [AddSubgroup.coe_add, AddSubgroup.coe_zsmul, hx]
  by_cases hsh : s ≤ h
  · left
    refine mem_bareBlock_of_axial hL c.source _ μ (ε * s) h hhz ?_ ?_
    · rcases hε with rfl | rfl <;> omega
    · rw [hcoe, add_sub_cancel_left]
  · right
    refine mem_bareBlock_of_axial hL c.target _ μ (ε * s - ε * N) h hhz ?_ ?_
    · rcases hε with rfl | rfl <;> omega
    · rw [hcoe, sub_zsmul, ← hd]
      abel
theorem bareBlockPairsAreSiteBoxes (hBox : CornerBoxProperties)
    (hU : CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) {q : ℕ}
    (hq : q ≤ K) : BareBlockPairsAreSiteBoxes L m K q := fun c =>
  ⟨(bareBlockPair_isSiteBox hBox hL hm hK hq c).1, (bareBlockPair_isSiteBox hBox hL hm hK hq c).2,
    (bareAxialPath_subset_bareBlockPair hU hL hm hq c).1,
    (bareAxialPath_subset_bareBlockPair hU hL hm hq c).2⟩
theorem inv_mem_compactGaugeGroup {g : Matrices.ComplexMatrix2} (h : g ∈ compactGaugeGroup) :
    g⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem inv_inv_of_mem_compactGaugeGroup {g : Matrices.ComplexMatrix2}
    (h : g ∈ compactGaugeGroup) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem isGaugeField_gaugeTransform {j : ℤ} {ℬ : Set (Bond L m j)}
    {U : Bond L m j → Matrices.ComplexMatrix2} {u : Site L m j → Matrices.ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup ℬ U)
    (hu : ∀ b ∈ ℬ, u b.source ∈ compactGaugeGroup ∧ u b.target ∈ compactGaugeGroup) :
    IsGaugeField compactGaugeGroup ℬ (gaugeTransform u U) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · exact Matrices.ComplexMatrix2.specialUnitary.mul_mem
      (Matrices.ComplexMatrix2.specialUnitary.mul_mem (hu b hb).1 (hU.1 b hb))
      (inv_mem_compactGaugeGroup (hu b hb).2)
  · change u b.target * U b.opposite * (u b.source)⁻¹ = (u b.source * U b * (u b.target)⁻¹)⁻¹
    rw [hU.2 b hb, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      inv_inv_of_mem_compactGaugeGroup (hu b hb).2, Matrix.mul_assoc]
theorem exists_extended_gaugeMap {j : ℤ} (D : Set (FourTorus L m)) {ℬ : Set (Bond L m j)}
    {U : Bond L m j → Matrices.ComplexMatrix2} (hU : IsGaugeField compactGaugeGroup ℬ U)
    (hsub : (bondsInside D : Set (Bond L m j)) ⊆ ℬ) {Y : Set (Site L m j)}
    {u : Site L m j → Matrices.ComplexMatrix2} (hY : (sitesIn D : Set (Site L m j)) ⊆ Y)
    (hu : ∀ x ∈ Y, u x ∈ compactGaugeGroup) :
    ∃ ũ : Site L m j → Matrices.ComplexMatrix2, IsGaugeMap compactGaugeGroup ũ ∧
      (∀ x ∈ Y, ũ x = u x) ∧
      extendByOne (bondsInside D) (gaugeTransform u U) ∈ compactGaugeFields L m j ∧
      gaugeTransform ũ (extendByOne (bondsInside D) U) ∈ compactGaugeFields L m j ∧
      ∀ b ∈ (bondsInside D : Set (Bond L m j)),
        extendByOne (bondsInside D) (gaugeTransform u U) b =
          gaugeTransform ũ (extendByOne (bondsInside D) U) b := by
  classical
  have hclD : IsReversalClosed (bondsInside D : Set (Bond L m j)) :=
    fun b hb => ⟨hb.2, hb.1⟩
  have hUD : IsGaugeField compactGaugeGroup (bondsInside D) U :=
    ⟨fun b hb => hU.1 b (hsub hb), fun b hb => hU.2 b (hsub hb)⟩
  let ũ : Site L m j → Matrices.ComplexMatrix2 := fun x => if x ∈ Y then u x else 1
  have hũY : ∀ x ∈ Y, ũ x = u x := fun x hx => if_pos hx
  have hũ : IsGaugeMap compactGaugeGroup ũ := by
    intro x
    by_cases hx : x ∈ Y
    · rw [hũY x hx]
      exact hu x hx
    · simp only [ũ, if_neg hx]
      exact Matrices.ComplexMatrix2.specialUnitary.one_mem
  have hE := extendByOne_mem_compactGaugeFields hclD hUD
  refine ⟨ũ, hũ, hũY, extendByOne_mem_compactGaugeFields hclD
    (isGaugeField_gaugeTransform hUD fun b hb => ⟨hu _ (hY hb.1), hu _ (hY hb.2)⟩),
    isGaugeField_gaugeTransform hE fun b _ => ⟨hũ _, hũ _⟩, fun b hb => ?_⟩
  have e1 : extendByOne (bondsInside D) (gaugeTransform u U) b = gaugeTransform u U b :=
    if_pos hb
  have e2 : extendByOne (bondsInside D) U b = U b := if_pos hb
  rw [e1]
  show _ = ũ b.source * extendByOne (bondsInside D) U b * (ũ b.target)⁻¹
  rw [e2, hũY _ (hY hb.1), hũY _ (hY hb.2)]
  rfl
theorem iterateFromLevel_zero_heq
    {f : ∀ k, (BondAtLevel L m K k → Matrices.ComplexMatrix2) →
      BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2}
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (n : ℕ) :
    HEq (iterateFromLevel f 0 n U) (iterateFromBare f n U) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have key : ∀ (k : ℕ) (_ : k = n) (A : BondAtLevel L m K k → Matrices.ComplexMatrix2)
        (B : BondAtLevel L m K n → Matrices.ComplexMatrix2), HEq A B → HEq (f k A) (f n B) := by
      rintro k rfl A B h
      rw [eq_of_heq h]
    exact key (0 + n) (Nat.zero_add n) _ _ ih
theorem blockFieldAtLevel_congr (hG : BlockAverageLocalityAndCovariance)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {q : ℕ} (hq : q ≤ K)
    (c : BondAtLevel L m K q) {W W' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2}
    (hW : W ∈ gaugeFieldsAtLevel L m K 0) (hW' : W' ∈ gaugeFieldsAtLevel L m K 0)
    (h : ∀ b ∈ (bondsInside (refinedBlock q c.source ∪ refinedBlock q c.target) :
      Set (BondAtLevel L m K 0)), W b = W' b) :
    blockFieldAtLevel (Averaging.smoothingRadius L) q W c =
      blockFieldAtLevel (Averaging.smoothingRadius L) q W' c := by
  have hR : BlockAverageIterLocal L m K 0 q := (hG L m K hL hm).2.1 0 q (by omega)
  have gen : ∀ (k : ℕ) (_ : 0 + q = k) (A A' : BondAtLevel L m K k → Matrices.ComplexMatrix2),
      HEq (blockAverageIter (K := K) (Averaging.smoothingRadius L) 0 q W) A →
      HEq (blockAverageIter (K := K) (Averaging.smoothingRadius L) 0 q W') A' →
      ∀ c : BondAtLevel L m K k,
        (∀ b ∈ (bondsInside (refinedBlock q c.source ∪ refinedBlock q c.target) :
          Set (BondAtLevel L m K 0)), W b = W' b) → A c = A' c := by
    rintro _ rfl A A' hA hA' c hc
    obtain rfl := eq_of_heq hA
    obtain rfl := eq_of_heq hA'
    exact hR c W hW W' hW' hc
  exact gen q (Nat.zero_add q) _ _ (iterateFromLevel_zero_heq W q)
    (iterateFromLevel_zero_heq W' q) c h
theorem blockAverageStep_congr (hG : BlockAverageLocalityAndCovariance)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hi : i < K)
    (c : BondAtLevel L m K (i + 1)) {W W' : BondAtLevel L m K i → Matrices.ComplexMatrix2}
    (hW : W ∈ gaugeFieldsAtLevel L m K i) (hW' : W' ∈ gaugeFieldsAtLevel L m K i)
    (h : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K i)), W b = W' b) :
    blockAverageStep (Averaging.smoothingRadius L) i W c =
      blockAverageStep (Averaging.smoothingRadius L) i W' c :=
  (hG L m K hL hm).2.1 i 1 (by omega) c W hW W' hW' h
theorem coe_toSublattice_mem_bareBlock (hL : Conventions.IsAdmissibleBlockingFactor L) {q : ℕ}
    (y : SiteAtLevel L m K q) :
    ((y.toSublattice (levelDepth K 0) : SiteAtLevel L m K 0) : FourTorus L m) ∈ bareBlock y := by
  show _ ∈ blockAtLevel 0 y
  rw [blockAtLevel_eq_cubeAtLevel_inter (Nat.zero_le q) y]
  refine ⟨?_, Subtype.coe_prop _⟩
  rw [coe_toSublattice_of_le hL (by simp only [levelDepth]; omega)]
  exact self_mem_cubeAround hL y
theorem partialBareBlockFieldLocalCovariant (hG : BlockAverageLocalityAndCovariance)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {q : ℕ} (hq : q ≤ K) :
    PartialBareBlockFieldLocalCovariant L m K q := by
  intro c ℬ U hgiven
  have hE := bareBlockPairExtension_mem hgiven
  refine ⟨fun U' hU' hag => ?_, fun Y u hY hu => ?_⟩
  · refine blockFieldAtLevel_congr hG hL hm hq c hE hU' fun b hb => ?_
    have hb' : b ∈ bareBondsInBlockPair c := hb
    have e : bareBlockPairExtension U c b = U b := if_pos hb'
    rw [e, hag b hb']
  · obtain ⟨ũ, hũ, hũY, hW1, hW2, hag⟩ := exists_extended_gaugeMap (bareBlockPair c)
      hgiven.2.1 hgiven.2.2 hY hu
    have hsource : c.source.toSublattice (levelDepth K 0) ∈ Y :=
      hY (Or.inl (coe_toSublattice_mem_bareBlock hL c.source))
    have htarget : c.target.toSublattice (levelDepth K 0) ∈ Y :=
      hY (Or.inr (coe_toSublattice_mem_bareBlock hL c.target))
    have hcov := ((hG L m K hL hm).2.2 q hq).1 _ hE ũ hũ
    calc partialBareBlockField (Averaging.smoothingRadius L) (gaugeTransform u U) c
        = blockFieldAtLevel (Averaging.smoothingRadius L) q
            (gaugeTransform ũ (bareBlockPairExtension U c)) c :=
          blockFieldAtLevel_congr hG hL hm hq c hW1 hW2 fun b hb => hag b hb
      _ = gaugeTransform (restrictGaugeMap q ũ)
            (blockFieldAtLevel (Averaging.smoothingRadius L) q (bareBlockPairExtension U c)) c :=
          congrFun hcov c
      _ = _ := by
          show ũ (c.source.toSublattice (levelDepth K 0)) * _ *
            (ũ (c.target.toSublattice (levelDepth K 0)))⁻¹ = _
          rw [hũY _ hsource, hũY _ htarget]
          rfl
theorem partialBlockAverageStepLocalCovariant (hG : BlockAverageLocalityAndCovariance)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hi : i < K) :
    PartialBlockAverageStepLocalCovariant L m K i := by
  intro c ℬ W hgiven
  have hE := doubleBlockExtension_mem hgiven
  refine ⟨fun W' hW' hag => ?_, fun Y u hY hu => ?_⟩
  · refine blockAverageStep_congr hG hL hm hi c hE hW' fun b hb => ?_
    have e : doubleBlockExtension W c b = W b := if_pos hb
    rw [e, hag b hb]
  · obtain ⟨ũ, hũ, hũY, hW1, hW2, hag⟩ := exists_extended_gaugeMap (bondDoubleBlock c)
      hgiven.2.1 hgiven.2.2 hY hu
    have hmem : ∀ y : SiteAtLevel L m K (i + 1),
        ((y.toSublattice (levelDepth K i) : SiteAtLevel L m K i) : FourTorus L m) ∈
          unitBlock y := by
      intro y
      have hle : levelDepth K (i + 1) ≤ levelDepth K i := by
        simp only [levelDepth]; push_cast; omega
      refine ⟨?_, ?_⟩
      · rw [coe_toSublattice_of_le hL hle]
        exact self_mem_cubeAround hL y
      · have e : levelDepth K (i + 1) + ((1 : ℕ) : ℤ) = levelDepth K i := by
          simp only [levelDepth]; push_cast; ring
        rw [e]
        exact Subtype.coe_prop _
    have hsource : c.source.toSublattice (levelDepth K i) ∈ Y := hY (Or.inl (hmem c.source))
    have htarget : c.target.toSublattice (levelDepth K i) ∈ Y := hY (Or.inr (hmem c.target))
    have hcov := ((hG L m K hL hm).1 i hi).1 _ hE ũ hũ
    calc partialBlockAverageStep (Averaging.smoothingRadius L) (gaugeTransform u W) c
        = blockAverageStep (Averaging.smoothingRadius L) i
            (gaugeTransform ũ (doubleBlockExtension W c)) c :=
          blockAverageStep_congr hG hL hm hi c hW1 hW2 fun b hb => hag b hb
      _ = gaugeTransform (restrictGaugeMap (i + 1) ũ)
            (blockAverage (Averaging.smoothingRadius L) (doubleBlockExtension W c)) c :=
          congrFun hcov.2.2 c
      _ = _ := by
          show ũ (c.source.toSublattice (levelDepth K i)) * _ *
            (ũ (c.target.toSublattice (levelDepth K i)))⁻¹ = _
          rw [hũY _ hsource, hũY _ htarget]
          rfl
theorem regionBlockAverageEqExtension (hC : StandardPartitionCubeGeometry)
    (hB : BlockPartition.Properties) (hT : CubesUnderRefinement)
    (hG : BlockAverageLocalityAndCovariance)
    (hDL : PartialAveragesAgreeWithBlockAverage.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) {q : ℕ}
    (hq : q ≤ K) : RegionBlockAverageEqExtension L m K q := by
  intro X hX U hU Ũ hŨ hag
  have hreg : ∀ k ≤ q, IsPartitionRegion (levelDepth K k) X := fun k hk =>
    (regionsOfNestedPartitions (K := K) hT hL hm k q hk (by omega) X hX).1
  have hcube : ∀ k ≤ q, ∀ y : SiteAtLevel L m K k, (y : FourTorus L m) ∈ X →
      cubeAround y ⊆ X := by
    intro k hk y hy
    have hx := self_mem_cubeAround hL y
    obtain ⟨-, -, h3⟩ := sitesInPartitionCubes (K := K) hC hB hL hm (le_refl k) (by omega) y
    exact ((h3 X (hreg k hk) (cubeAround y) ⟨y, rfl⟩ hx).1.1 hy).2
  have hclX : ∀ (k : ℕ), IsReversalClosed (bondsInside X : Set (BondAtLevel L m K k)) :=
    fun k b hb => ⟨hb.2, hb.1⟩
  have first : ∀ i : ℕ, i ≤ q → ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K i)),
      regionBlockAverage X U i c = blockFieldAtLevel (Averaging.smoothingRadius L) i Ũ c := by
    intro i
    induction i with
    | zero =>
      intro _ c hc
      exact (hag c hc).symm
    | succ i ih =>
      intro hi c hc
      have ih' := ih (by omega)
      have hF : blockFieldAtLevel (Averaging.smoothingRadius L) i Ũ ∈
          gaugeFieldsAtLevel L m K i :=
        ((hDL L m K hL hm 0 hK).2.1 Ũ hŨ i (by omega)).2
      have hfield : IsGaugeField compactGaugeGroup (bondsInside X : Set (BondAtLevel L m K i))
          (regionBlockAverage X U i) := by
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · rw [ih' b hb]
          exact hF.1 b (mem_univ b)
        · rw [ih' b hb, ih' _ (hclX i b hb)]
          exact hF.2 b (mem_univ b)
      have hE := extendByOne_mem_compactGaugeFields (hclX i) hfield
      refine blockAverageStep_congr hG hL hm (by omega) c hE hF fun b hb => ?_
      have hsubX : bondDoubleBlock c ⊆ X := by
        rintro z (hz | hz)
        · exact hcube _ hi _ hc.1 hz.1
        · exact hcube _ hi _ hc.2 hz.1
      have hbX : b ∈ (bondsInside X : Set (BondAtLevel L m K i)) := ⟨hsubX hb.1, hsubX hb.2⟩
      have e : extendByOne (bondsInside X) (regionBlockAverage X U i) b =
        regionBlockAverage X U i b := if_pos hbX
      exact e.trans (ih' b hbX)
  refine ⟨first, fun c hc => ?_⟩
  have hsub : bareBlockPair c ⊆ X := by
    rintro z (hz | hz)
    · rw [blockAtLevel_eq_cubeAtLevel_inter (Nat.zero_le q)] at hz
      exact hcube q le_rfl _ hc.1 hz.1
    · rw [blockAtLevel_eq_cubeAtLevel_inter (Nat.zero_le q)] at hz
      exact hcube q le_rfl _ hc.2 hz.1
  refine ⟨hsub, ?_⟩
  have hbonds : bareBondsInBlockPair c ⊆ (bondsInside X : Set (BondAtLevel L m K 0)) :=
    fun b hb => ⟨hsub hb.1, hsub hb.2⟩
  have hgiven : IsDefinedOnBareBlockPair (bondsInside X) U c := ⟨hclX 0, hU, hbonds⟩
  rw [first q le_rfl c hc]
  exact ((partialBareBlockFieldLocalCovariant hG hL hm hq c _ U hgiven).1 Ũ hŨ
    fun b hb => hag b (hbonds hb)).symm
theorem holds
    (hC : StandardPartitionCubeGeometry) (hB : BlockPartition.Properties)
    (hBox : CornerBoxProperties) (hT : CubesUnderRefinement)
    (hG : BlockAverageLocalityAndCovariance)
    (hU : CoordinateDescription)
    (hDL : PartialAveragesAgreeWithBlockAverage.Statement) :
    GeometryAndLocalityOfBlockAverages.Statement := by
  intro L m K hL hm hK
  exact ⟨sublatticesAndCubesInBareUnits hC hU hL hm hK,
    fun i q _ hiq hq => sitesInPartitionCubes hC hB hL hm hiq hq,
    regionsOfNestedPartitions hT hL hm,
    complementRegionIndependentOfScale hC hL hm,
    fun i q hiq hq => blocksAtLevelAreSiteBoxes hBox hL hm hK hiq hq,
    fun q hq => bareBlockPairsAreSiteBoxes hBox hU hL hm hK hq,
    fun q hq => partialBareBlockFieldLocalCovariant hG hL hm hq,
    fun i hi => partialBlockAverageStepLocalCovariant hG hL hm hi,
    fun q hq => regionBlockAverageEqExtension hC hB hT hG hDL hL hm hK hq,
    fun i hi => sitesOfRegionDifference hC hB hL hm hi⟩
end PeriodicLattice.GeometryAndLocalityOfBlockAverages
end YangMills.Construction
