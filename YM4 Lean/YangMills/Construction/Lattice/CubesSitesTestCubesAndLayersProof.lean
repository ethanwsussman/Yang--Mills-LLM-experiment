import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.CubeSizesAndTheLeastDepth
import YangMills.Construction.Lattice.CubesLayersAndTopsOfADecreasingSequenceProof
import YangMills.Construction.Lattice.CubesSitesTestCubesAndLayers
import YangMills.Construction.Lattice.LocalityAndGaugeCovarianceOfTheAveragingMap
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric ParameterChoice
noncomputable section
namespace PeriodicLattice
namespace PartitionGeometry
variable {L m : ℕ}
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem norm_torusProj_le {S r : ℝ} (hr : 0 ≤ r) {v : Fin 4 → ℝ} (h : ∀ μ, |v μ| ≤ r) :
    ‖torusProj S v‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 fun μ => (addCircle_norm_coe_le_abs (v μ)).trans (h μ)
theorem exists_torusProj_eq_abs_eq_norm {S : ℝ} (d : Torus4 S) :
    ∃ v, torusProj S v = d ∧ ∀ μ, |v μ| = ‖d μ‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.exists_torusProj_eq_abs_eq_norm <;> assumption
theorem torusProj_sub {S : ℝ} (u v : Fin 4 → ℝ) :
    torusProj S (u - v) = torusProj S u - torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem exists_abs_le_abs_sub_le (v : ℝ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : |v| ≤ r + s) : ∃ t, |t| ≤ r ∧ |v - t| ≤ s := by
  rcases le_or_gt |v| r with h' | h'
  · exact ⟨v, h', by simpa using hs⟩
  · rcases le_total 0 v with h0 | h0
    · rw [abs_of_nonneg h0] at h h'
      refine ⟨r, by rw [abs_of_nonneg hr], ?_⟩
      rw [abs_of_pos (by linarith)]
      linarith
    · rw [abs_of_nonpos h0] at h h'
      refine ⟨-r, by rw [abs_neg, abs_of_nonneg hr], ?_⟩
      rw [abs_of_neg (by linarith)]
      linarith
theorem exists_norm_le_norm_sub_le {S r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (d : Torus4 S)
    (h : ‖d‖ ≤ r + s) : ∃ e : Torus4 S, ‖e‖ ≤ r ∧ ‖d - e‖ ≤ s := by
  obtain ⟨v, hv, hv'⟩ := exists_torusProj_eq_abs_eq_norm d
  have hle : ∀ μ, |v μ| ≤ r + s := fun μ => by
    rw [hv' μ]
    exact (norm_le_pi_norm d μ).trans h
  choose t ht ht' using fun μ => exists_abs_le_abs_sub_le (v μ) hr hs (hle μ)
  refine ⟨torusProj S t, norm_torusProj_le hr ht, ?_⟩
  rw [← hv, ← torusProj_sub]
  exact norm_torusProj_le hs ht'
theorem exists_int_abs_le_abs_sub_mul_le (b : ℕ) {W t : ℝ} (hW : 0 < W)
    (h : |t| ≤ (b : ℝ) * W + W / 2) :
    ∃ p : ℤ, |(p : ℝ)| ≤ b ∧ |t - (p : ℝ) * W| ≤ W / 2 := by
  have hr := abs_sub_round (t / W)
  set r := round (t / W) with hrdef
  have hscale : ∀ p : ℤ, |t / W - (p : ℝ)| ≤ 1 / 2 → |t - (p : ℝ) * W| ≤ W / 2 := by
    intro p hp
    have : t - (p : ℝ) * W = (t / W - (p : ℝ)) * W := by field_simp
    rw [this, abs_mul, abs_of_pos hW]
    nlinarith
  rw [abs_le] at h
  have hlo : -(b : ℝ) - 1 / 2 ≤ t / W := by
    rw [le_div_iff₀ hW]; nlinarith [h.1]
  have hhi : t / W ≤ (b : ℝ) + 1 / 2 := by
    rw [div_le_iff₀ hW]; nlinarith [h.2]
  rw [abs_le] at hr
  by_cases hra : r < -(b : ℤ)
  · refine ⟨-(b : ℤ), by simp, hscale _ ?_⟩
    have : (r : ℝ) + 1 ≤ ((-(b : ℤ) : ℤ) : ℝ) := by exact_mod_cast hra
    push_cast at this ⊢
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  by_cases hrb : (b : ℤ) < r
  · refine ⟨(b : ℤ), by simp, hscale _ ?_⟩
    have : ((b : ℤ) : ℝ) + 1 ≤ r := by exact_mod_cast hrb
    push_cast at this ⊢
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  · refine ⟨r, ?_, hscale r (abs_le.2 hr)⟩
    have h1 : -(b : ℝ) ≤ r := by exact_mod_cast not_lt.1 hra
    have h2 : (r : ℝ) ≤ b := by exact_mod_cast not_lt.1 hrb
    exact abs_le.2 ⟨h1, h2⟩
theorem exists_gridPoint_near {S W : ℝ} (hW : 0 < W) (b : ℕ) (d : Torus4 S)
    (h : ‖d‖ ≤ (b : ℝ) * W + W / 2) :
    ∃ p : Fin 4 → ℤ, ‖torusProj S fun μ => (p μ : ℝ) * W‖ ≤ (b : ℝ) * W ∧
      ‖d - torusProj S fun μ => (p μ : ℝ) * W‖ ≤ W / 2 := by
  obtain ⟨v, hv, hv'⟩ := exists_torusProj_eq_abs_eq_norm d
  have hle : ∀ μ, |v μ| ≤ (b : ℝ) * W + W / 2 := fun μ => by
    rw [hv' μ]
    exact (norm_le_pi_norm d μ).trans h
  choose p hp hp' using fun μ => exists_int_abs_le_abs_sub_mul_le b hW (hle μ)
  refine ⟨p, norm_torusProj_le (by positivity) fun μ => ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hW]
    exact mul_le_mul_of_nonneg_right (hp μ) hW.le
  · rw [← hv, ← torusProj_sub]
    exact norm_torusProj_le (by positivity) hp'
theorem meshSize_pos_of_pos (hL : 0 < L) (i : ℤ) : 0 < meshSize L i := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem meshSize_eq_pow_mul (hL : 0 < L) (i : ℤ) (n : ℕ) :
    meshSize L i = (L : ℝ) ^ n * meshSize L (i + n) := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.meshSize_eq_pow_mul <;> assumption
theorem mem_cubeAround_iff {i : ℤ} {y : Site L m i} {x : FourTorus L m} :
    x ∈ cubeAround y ↔ ‖x - (y : FourTorus L m)‖ ≤ meshSize L i / 2 := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.mem_cubeAround <;> assumption
theorem self_mem_cubeAround (hL : 0 < L) {i : ℤ} (y : Site L m i) :
    (y : FourTorus L m) ∈ cubeAround y := by apply _root_.YangMills.Construction.SeparatedSequences.AntitoneBlocks.centre_mem_cubeAround <;> assumption
theorem siteInteriorToCoarseCube (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hcubes : StandardPartitionCubeGeometry) (hblocks : BlockPartition.Properties)
    {i : ℤ} (hi : -(m : ℤ) ≤ i) (n : ℕ) (x : Site L m (i + n)) :
    SiteInteriorToCoarseCube L m i n x := by
  obtain ⟨hR, hD, -, -, -⟩ := hcubes L m hL.1 hL.2 hm i hi
  have hR := hR n
  have hP := (hblocks L m hL hm i n 0 hi).2.1
  have hL0 : 0 < L := by have := hL.2; omega
  have hW' : 0 < meshSize L (i + n) := meshSize_pos_of_pos hL0 _
  have hx : (x : FourTorus L m) ∈ ⋃ y : Site L m i, refinedBlock n y := by
    rw [hP.2.2.2]
    exact x.2
  obtain ⟨y, hy⟩ := mem_iUnion.1 hx
  rw [hR.1 y] at hy
  obtain ⟨p, hp, hxy⟩ := hy
  have hclose : ‖(x : FourTorus L m) - (y : FourTorus L m)‖ < meshSize L i / 2 := by
    have hsub : (x : FourTorus L m) - y =
        torusProj (torusSide L m) fun μ => meshSize L (i + n) * (p μ : ℝ) := by
      rw [hxy]
      abel
    rw [hsub]
    have hb : ∀ μ, |meshSize L (i + n) * (p μ : ℝ)| ≤
        ((L : ℝ) ^ n - 1) / 2 * meshSize L (i + n) := by
      intro μ
      rw [abs_mul, abs_of_pos hW', mul_comm]
      exact mul_le_mul_of_nonneg_right (hp μ) hW'.le
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ (by exact_mod_cast hL0)
    refine (norm_torusProj_le (mul_nonneg (by linarith) hW'.le) hb).trans_lt ?_
    rw [meshSize_eq_pow_mul hL0 i n]
    have : ((L : ℝ) ^ n - 1) / 2 * meshSize L (i + n) =
        (L : ℝ) ^ n * meshSize L (i + n) / 2 - meshSize L (i + n) / 2 := by ring
    rw [this]
    linarith
  have hclose' : ∀ z : FourTorus L m, ‖z - (y : FourTorus L m)‖ < meshSize L i / 2 →
      ∀ Q ∈ standardCubePartition L m i, z ∈ Q → Q = cubeAround y := by
    intro z hz
    exact hD.2.2.2.2.2.1 y z (by rw [torusSupNorm_eq_norm]; exact hz)
  have hball : Metric.ball (y : FourTorus L m) (meshSize L i / 2) ⊆ cubeAround y :=
    fun z hz => mem_cubeAround_iff.2 (mem_ball_iff_norm.1 hz).le
  have hxball : (x : FourTorus L m) ∈ Metric.ball (y : FourTorus L m) (meshSize L i / 2) :=
    mem_ball_iff_norm.2 hclose
  have hnhds : cubeAround y ∈ nhds (x : FourTorus L m) :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxball) hball
  have hxQ : (x : FourTorus L m) ∈ cubeAround y := hball hxball
  have huniq : ∀ Q' ∈ standardCubePartition L m i, (x : FourTorus L m) ∈ Q' →
      Q' = cubeAround y :=
    hclose' _ hclose
  have hcube : cubeAround x ⊆ cubeAround y := by
    obtain ⟨Q', hQ', hs⟩ := hR.2.2.1 (cubeAround x) ⟨x, rfl⟩
    rw [← huniq Q' hQ' (hs (self_mem_cubeAround hL0 x))]
    exact hs
  unfold SiteInteriorToCoarseCube
  refine ⟨?_, cubeAround y, ⟨y, rfl⟩, ⟨hxQ, huniq⟩, hnhds, ?_, hcube,
    fun n' z hz => hcube hz.1⟩
  · intro Q' hQ' hfr
    rw [frontier, mem_sdiff] at hfr
    by_cases hQ : Q' = cubeAround y
    · rw [hQ] at hfr
      exact hfr.2 (mem_interior_iff_mem_nhds.2 hnhds)
    · obtain ⟨z, hz, hzQ⟩ := mem_closure_iff.1 hfr.1 _ Metric.isOpen_ball hxball
      exact hQ (hclose' z (mem_ball_iff_norm.1 hz) Q' hQ' hzQ)
  · intro X hX
    constructor
    · intro hxX
      obtain ⟨Q', hQ', hxQ'⟩ := (mem_iff_exists_partitionCube hX _).1 hxX
      rw [← huniq Q' hQ'.1 hxQ']
      exact hQ'
    · intro h
      exact h.2 hxQ
theorem coarserPartitionRefines (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hcubes : StandardPartitionCubeGeometry) (hblocks : BlockPartition.Properties)
    {i i' : ℤ} (hi : -(m : ℤ) ≤ i) (hii : i ≤ i') : CoarserPartitionRefines L m i i' := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i' = i + n := ⟨(i' - i).toNat, by omega⟩
  have hR := (hcubes L m hL.1 hL.2 hm i hi).1 n
  have hL0 : 0 < L := by have := hL.2; omega
  unfold CoarserPartitionRefines
  refine ⟨?_, ?_, hR.2.2.2.1⟩
  · rintro _ ⟨y, rfl⟩
    have h := hR.2.1 y
    apply subset_antisymm
    · intro z hz
      rw [h] at hz
      simp only [mem_iUnion] at hz
      obtain ⟨y', hy', hz'⟩ := hz
      refine ⟨cubeAround y', ⟨⟨y', rfl⟩, ?_⟩, hz'⟩
      intro w hw
      rw [h]
      simp only [mem_iUnion]
      exact ⟨y', hy', hw⟩
    · exact sUnion_subset fun Q hQ => hQ.2
  · rintro _ ⟨x, rfl⟩
    obtain ⟨-, Q, hQ, ⟨-, hu⟩, -, -, hs, -⟩ :=
      siteInteriorToCoarseCube hL hm hcubes hblocks hi n x
    exact ⟨Q, ⟨hQ, hs⟩, fun Q₂ h₂ => hu Q₂ h₂.1 (h₂.2 (self_mem_cubeAround hL0 x))⟩
theorem testPartitionSubordinate (hcubes : StandardPartitionCubeGeometry)
    (hblocks : BlockPartition.Properties)
    (hsizes : CubesOfStep.CubeSizesAndMinimalDelay)
    (c : ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ)
    (hpar : CubesOfStep.LargeFieldParameters c K x) (hm : 0 < m) (k : ℕ) (hk : k < K)
    (hfit : CubesOfStep.PartitionsFit c m K x (k + 1)) :
    TestPartitionSubordinate c m K x k := by
  have hL := hpar.factor_admissible
  have hL1 : 1 < c.L := by have := hL.2; omega
  obtain ⟨e₁, -, he₁⟩ := hpar.M₁_isPow
  obtain ⟨e₂, -, he₂⟩ := hpar.M_isPow
  obtain ⟨⟨b, hb⟩, -, -⟩ := (hsizes c K x hL hpar.two_le_r hpar.one_lt_coupling).1 (k + 1) hk
  have hsize : CubesOfStep.blockSizeAt c x (k + 1) = c.L ^ b := hb
  have hbase : CubesOfStep.secondSize c = c.L ^ (2 + e₁) := by
    unfold CubesOfStep.secondSize secondCubeSize
    rw [he₁, pow_add]
  have hcoarseSide : CubesOfStep.coarseCubeSide c x k = c.L ^ (1 + e₂ + b) := by
    unfold CubesOfStep.coarseCubeSide
    rw [hsize, he₂]
    ring
  have hcoarse : CubesOfStep.coarsePartitionIndex c K x k = (K : ℤ) - k - (1 + e₂ + b) := by
    unfold CubesOfStep.coarsePartitionIndex CubesOfStep.partitionIndexOfSize scaledCubeIndex
    rw [hcoarseSide, Nat.log_pow hL1]
    push_cast
    ring
  have htest : CubesOfStep.testPartitionIndex c K x k = (K : ℤ) - k - (4 + e₁ + b) := by
    unfold CubesOfStep.testPartitionIndex CubesOfStep.partitionIndexOfSize scaledCubeIndex
    have : c.L ^ 2 * CubesOfStep.secondSize c * CubesOfStep.blockSizeAt c x (k + 1) =
        c.L ^ (4 + e₁ + b) := by
      rw [hsize, hbase]
      ring
    rw [this, Nat.log_pow hL1]
    push_cast
    ring
  have hdensity : CubesOfStep.densityPartitionIndex c K x (k + 1) =
      (K : ℤ) - k - (4 + e₁ + b) := by
    unfold CubesOfStep.densityPartitionIndex CubesOfStep.partitionIndexOfSize scaledCubeIndex
    have : c.L * CubesOfStep.secondSize c * CubesOfStep.blockSizeAt c x (k + 1) =
        c.L ^ (3 + e₁ + b) := by
      rw [hsize, hbase]
      ring
    rw [this, Nat.log_pow hL1]
    simp only [levelDepth]
    omega
  have hfits : e₂ + b ≤ m + K - (k + 1) := by
    have h : c.M * CubesOfStep.blockSizeAt c x (k + 1) ≤ c.L ^ (m + K - (k + 1)) := hfit
    rw [hsize, he₂, ← pow_add] at h
    exact (Nat.pow_le_pow_iff_right hL1).1 h
  have hfour : 4 + e₁ ≤ e₂ := by
    have h := hpar.pow_four_mul_le
    rw [he₁, he₂, ← pow_add] at h
    exact (Nat.pow_le_pow_iff_right hL1).1 h
  have hlow : -(m : ℤ) ≤ CubesOfStep.coarsePartitionIndex c K x k := by
    rw [hcoarse]
    omega
  have hle : CubesOfStep.coarsePartitionIndex c K x k ≤
      CubesOfStep.testPartitionIndex c K x k := by
    rw [hcoarse, htest]
    omega
  have hA : CoarserPartitionRefines c.L m _ _ :=
    coarserPartitionRefines hL hm hcubes hblocks hlow hle
  have hsub : SubordinateToCoarsePartition (m := m) c K x k
      (CubesOfStep.testPartition c K x k) := by
    unfold SubordinateToCoarsePartition
    refine ⟨hA.2.1, fun X hX => ?_⟩
    obtain ⟨C, hC, rfl⟩ := hA.2.2 X hX
    exact ⟨C, hC, rfl⟩
  have hsame : (CubesOfStep.densityPartition c K x (k + 1) : Set (Set (FourTorus c.L m))) =
      CubesOfStep.testPartition c K x k := by
    unfold CubesOfStep.densityPartition CubesOfStep.testPartition
    rw [hdensity, htest]
  unfold TestPartitionSubordinate
  exact ⟨hsub, hsame, by rw [hsame]; exact hsub⟩
theorem exists_pair_norm_sub_le_of_setSupDist_le (hL : 0 < L) {Q Y : Set (FourTorus L m)}
    (hQ : IsClosed Q) (hY : IsClosed Y) (hQn : Q.Nonempty) (hYn : Y.Nonempty) {r : ℝ}
    (hr : 0 ≤ r) (h : setSupDist Q Y ≤ ENNReal.ofReal r) :
    ∃ z ∈ Q, ∃ ω ∈ Y, ‖z - ω‖ ≤ r := by
  have : Fact (0 < torusSide L m) := ⟨by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    unfold torusSide
    positivity⟩
  have hcomp : IsCompact (Q ×ˢ Y) := hQ.isCompact.prod hY.isCompact
  obtain ⟨⟨z, ω⟩, hzω, hmin⟩ := hcomp.exists_isMinOn (hQn.prod hYn)
    (f := fun p : FourTorus L m × FourTorus L m => ‖p.1 - p.2‖) (by fun_prop)
  refine ⟨z, hzω.1, ω, hzω.2, ?_⟩
  have hle : ENNReal.ofReal ‖z - ω‖ ≤ setSupDist Q Y := by
    refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    rw [torusSupNorm_eq_norm]
    exact ENNReal.ofReal_le_ofReal (isMinOn_iff.1 hmin (a, b) (mk_mem_prod ha hb))
  exact (ENNReal.ofReal_le_ofReal_iff hr).1 (hle.trans h)
theorem layerNeighborhoodCharacterization (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hcubes : StandardPartitionCubeGeometry) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    (Y : Set (FourTorus L m)) (hne : Y.Nonempty) (hcl : IsClosed Y) (a : ℕ) (ha : 1 ≤ a) :
    LayerNeighborhoodCharacterization L m i Y a := by
  obtain ⟨-, hD, hE, -, -⟩ := hcubes L m hL.1 hL.2 hm i hi
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hL0 : 0 < L := by have := hL.2; omega
  have hW : 0 < meshSize L i := meshSize_pos_of_pos hL0 i
  have hcast : (((b + 1 : ℕ) : ℤ) - 1) = (b : ℤ) := by
    push_cast
    ring
  have hcastR : (((b + 1 : ℕ) : ℝ) - 1) * meshSize L i = (b : ℝ) * meshSize L i := by
    push_cast
    ring
  have hreg : IsPartitionRegion i (cubeHull i Y) := ⟨_, fun Q hQ => hQ.1, rfl⟩
  have hhull : ∀ y : Site L m i,
      cubeAround y ∈ partitionCubesIn i (cubeHull i Y) ↔ CubeIntersects (cubeAround y) Y := by
    intro y
    constructor
    · rintro ⟨-, hsub⟩
      exact (hD.2.2.2.2.2.2 {Q | Q ∈ standardCubePartition L m i ∧ CubeIntersects Q Y}
        (fun Q hQ => hQ.1) (cubeAround y) ⟨y, rfl⟩ hsub).2
    · intro h
      exact ⟨⟨y, rfl⟩, subset_sUnion_of_mem ⟨⟨y, rfl⟩, h⟩⟩
  unfold LayerNeighborhoodCharacterization
  constructor
  · rintro _ ⟨y', rfl⟩
    have hlay : layerNeighborhood i Y ((b + 1 : ℕ) : ℤ) =
        layerEnlargement i (cubeHull i Y) (b : ℤ) := by
      unfold layerNeighborhood
      rw [hcast]
    rw [hlay, hE.1 _ hreg b y', hcastR]
    have hbW : 0 ≤ (b : ℝ) * meshSize L i := by positivity
    constructor
    · rintro ⟨y, hy, hyy⟩
      obtain ⟨ω, hωQ, hωY⟩ := (hhull y).1 hy
      rw [torusSupNorm_eq_norm] at hyy
      have hd : ‖ω - (y' : FourTorus L m)‖ ≤ meshSize L i / 2 + (b : ℝ) * meshSize L i := by
        have e : ω - (y' : FourTorus L m) = (ω - y) - ((y' : FourTorus L m) - y) := by abel
        rw [e]
        exact (norm_sub_le _ _).trans (add_le_add (mem_cubeAround_iff.1 hωQ) hyy)
      obtain ⟨e, he, he'⟩ := exists_norm_le_norm_sub_le (half_pos hW).le hbW _ hd
      have hmem : (y' : FourTorus L m) + e ∈ cubeAround y' := by
        rw [mem_cubeAround_iff]
        simpa using he
      refine iInf₂_le_of_le _ hmem (iInf₂_le_of_le ω hωY (ENNReal.ofReal_le_ofReal ?_))
      rw [torusSupNorm_eq_norm]
      have e' : (y' : FourTorus L m) + e - ω = -(ω - (y' : FourTorus L m) - e) := by abel
      rw [e', norm_neg]
      exact he'
    · intro h
      have hclosed : IsClosed (cubeAround y') := by
        have : cubeAround y' = Metric.closedBall (y' : FourTorus L m) (meshSize L i / 2) := by
          ext z
          rw [mem_cubeAround_iff, mem_closedBall_iff_norm]
        rw [this]
        exact Metric.isClosed_closedBall
      obtain ⟨z, hz, ω, hωY, hzω⟩ := exists_pair_norm_sub_le_of_setSupDist_le hL0 hclosed hcl
        ⟨_, self_mem_cubeAround hL0 y'⟩ hne hbW h
      have hd : ‖ω - (y' : FourTorus L m)‖ ≤ (b : ℝ) * meshSize L i + meshSize L i / 2 := by
        have e : ω - (y' : FourTorus L m) = -(z - ω) + (z - y') := by abel
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add ?_ (mem_cubeAround_iff.1 hz))
        rw [norm_neg]
        exact hzω
      obtain ⟨p, hp, hp'⟩ := exists_gridPoint_near hW b _ hd
      let s : Site L m i :=
        ⟨torusProj (torusSide L m) fun μ => (p μ : ℝ) * meshSize L i, p, fun μ => rfl⟩
      refine ⟨y' + s, (hhull _).2 ⟨ω, ?_, hωY⟩, ?_⟩
      · rw [mem_cubeAround_iff]
        have e : ω - ((y' + s : Site L m i) : FourTorus L m) =
            ω - (y' : FourTorus L m) -
              torusProj (torusSide L m) fun μ => (p μ : ℝ) * meshSize L i := by
          show ω - ((y' : FourTorus L m) + _) = _
          abel
        rw [e]
        exact hp'
      · rw [torusSupNorm_eq_norm]
        have e : (y' : FourTorus L m) - ((y' + s : Site L m i) : FourTorus L m) =
            -torusProj (torusSide L m) fun μ => (p μ : ℝ) * meshSize L i := by
          show (y' : FourTorus L m) - ((y' : FourTorus L m) + _) = _
          abel
        rw [e, norm_neg]
        exact hp
  · intro hY
    have hhe : cubeHull i Y = addCubeLayer i Y := by
      unfold cubeHull addCubeLayer
      congr 1
      ext Q
      constructor
      · rintro ⟨hQ, z, hzQ, hzY⟩
        obtain ⟨Q', hQ', hz'⟩ := (mem_iff_exists_partitionCube hY z).1 hzY
        exact ⟨hQ, Q', hQ', z, hzQ, hz'⟩
      · rintro ⟨hQ, Q', hQ', z, hzQ, hz'⟩
        exact ⟨hQ, z, hzQ, hQ'.2 hz'⟩
    rw [hcast, hhe]
    show (addCubeLayer i)^[b] (addCubeLayer i Y) = (addCubeLayer i)^[b + 1] Y
    rw [Function.iterate_succ_apply]
end PartitionGeometry
theorem partitionGeometryStatement_holds
    (hcubes : StandardPartitionCubeGeometry) (hblocks : BlockPartition.Properties)
    (hlocal : BlockAverageLocalityAndCovariance)
    (hsizes : CubesOfStep.CubeSizesAndMinimalDelay) :
    PartitionGeometryStatement := by
  unfold PartitionGeometryStatement
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro L m hL hm i i' hi hii
    exact PartitionGeometry.coarserPartitionRefines hL hm hcubes hblocks hi hii
  · intro L m hL hm i n hi x
    exact PartitionGeometry.siteInteriorToCoarseCube hL hm hcubes hblocks hi n x
  · intro L m K hL hm k hk c hc V hV V' hV' h
    exact (((hlocal L m K hL hm).1 k hk).2.2.1 c hc V hV V' hV' fun b hb => h b hb).1
  · intro c m K x hpar hm k hk hfit
    exact PartitionGeometry.testPartitionSubordinate hcubes hblocks hsizes c m K x hpar hm k hk
      hfit
  · intro L m hL hm i hi Y hne hcl a ha
    exact PartitionGeometry.layerNeighborhoodCharacterization hL hm hcubes hi Y hne hcl a ha
end PeriodicLattice
end
end YangMills.Construction
