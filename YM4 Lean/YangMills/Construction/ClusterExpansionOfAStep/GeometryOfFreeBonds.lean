import YangMills.Construction.ClusterExpansionOfAStep.BlocksOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.ChainOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.HessianFloorOfTheCostForm
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.SharesAddToTheAction
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps TorusBlocks TorusFrame
  StepSettings StepCosts StepMarks LevelAction
variable {R : StepSetup} {n : ℕ} [NeZero n]
def StepSettings.ChartSetting.coolRegion (s : ChartSetting R n) : Finset (TorusSite (n * R.params.side)) :=
  Finset.univ \ thickening lumpRange (torusHotSites R.params s.fine)
def StepSettings.ChartSetting.sitesUnderRegion (s : ChartSetting R n) : Finset (TorusSite (n * R.params.side)) :=
  sitesInBlocks R.params.side s.region
def StepSettings.ChartSetting.IsNearFree (s : ChartSetting R n) (b : TorusBond (n * R.params.side)) : Prop :=
  ∃ b₀ ∈ s.free, supDist b₀.1 b.1 ≤ 2 * R.range + 2
structure StepSettings.StepSetup.IsLargeRange (R : StepSetup) : Prop where
  range_large : 64 * R.params.side + 2 ^ 16 ≤ R.range
  range_le_succ : R.range ≤ R.nextRange + 1
namespace FreeBonds
theorem mem_coolRegion_of_near_free {s : ChartSetting R n} (hs : s.IsAdmissible) (hR : R.IsLargeRange)
    {b₀ : TorusBond (n * R.params.side)} (hb : b₀ ∈ s.free)
    {y : TorusSite (n * R.params.side)} (hy : supDist b₀.1 y ≤ 3 * R.range) : y ∈ s.coolRegion := by
  unfold StepSettings.ChartSetting.coolRegion
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
  obtain ⟨z, hz, hd⟩ := (mem_thickening _ _ _).mp h
  have h1 := hs.far_from_support b₀ hb z (Finset.mem_union_right _ hz)
  have h2 := supDist_triangle b₀.1 y z
  have h3 := hR.range_large
  have h4 : lumpRange = 2 ^ 12 := rfl
  omega
theorem parentBlock_mem_region_of_near_free {s : ChartSetting R n} (hs : s.IsAdmissible) (hR : R.IsLargeRange)
    {b₀ : TorusBond (n * R.params.side)} (hb : b₀ ∈ s.free)
    {y : TorusSite (n * R.params.side)} (hy : supDist b₀.1 y ≤ 3 * R.range) :
    parentBlock R.params.side y ∈ s.region := by
  rcases hs.region_spec with ⟨h1, -⟩ | ⟨-, h1, h2⟩
  · rw [h1]
    exact Finset.mem_univ _
  · rw [h1]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
    obtain ⟨z, hz, hd⟩ := (mem_thickening _ _ _).mp h
    have h3 : parentBlock R.params.side y ∈ thickening (2 * R.nextRange) (torusHotSites R.params s.coarse) := by
      refine (mem_thickening _ _ _).mpr ⟨z, hz, ?_⟩
      have h4 := hR.range_large
      have h5 := hR.range_le_succ
      have h6 : lumpRange = 2 ^ 12 := rfl
      omega
    have h4 := h2 b₀ hb y h3
    have h5 := hR.range_large
    omega
end FreeBonds
theorem StepSettings.ChartSetting.exists_stepSituation {s : ChartSetting R n} (hs : s.IsAdmissible)
    (hn : R.params.n₀ ≤ n) :
    ∃ (C : Finset (TorusSite n)) (σ' : ℝ), IsStepSituation R.params R.nextRange s.coarse s.region C σ' ∧
      ∀ b ∈ s.free, ∀ z : TorusSite (n * R.params.side), parentBlock R.params.side z ∈ C →
        4 * R.range ≤ supDist b.1 z + R.params.side + 1 := by
  rcases hs.region_spec with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact ⟨∅, 9 / 8 * R.params.threshold, Or.inr ⟨hn, h2, h1, rfl, rfl⟩, fun _ _ _ hz => absurd hz (by simp)⟩
  · exact ⟨minimalHull R.params R.nextRange s.coarse, R.params.threshold, Or.inl ⟨h1, h2, rfl, rfl⟩, h3⟩
namespace FreeBonds
omit [NeZero n] in
theorem parentBlock_not_mem_of_near_free {s : ChartSetting R n} (hR : R.IsLargeRange) {C : Finset (TorusSite n)}
    (hC : ∀ b ∈ s.free, ∀ z : TorusSite (n * R.params.side), parentBlock R.params.side z ∈ C →
      4 * R.range ≤ supDist b.1 z + R.params.side + 1)
    {b₀ : TorusBond (n * R.params.side)} (hb : b₀ ∈ s.free) {y : TorusSite (n * R.params.side)}
    (hy : supDist b₀.1 y ≤ 3 * R.range) :
    parentBlock R.params.side y ∉ C := fun h => by
  have h1 := hC b₀ hb y h
  have h2 := hR.range_large
  omega
theorem isRegularRegion_of_torusFrame (L m : ℕ) [NeZero m] {X : Finset (TorusSite m)}
    (h : IsOrthantRegular (cellsOfSites (torusFrame L 0 m) X) 2047) : IsRegularRegion X 1024 := by
  have hn : ∀ i, (torusFrame L 0 m).extent i = m := fun _ => rfl
  intro z
  obtain ⟨eps, he, hr⟩ := h (torusSiteInFrame (torusFrame L 0 m) (torusFrame L 0 m).top z)
  refine ⟨eps, he, fun q hq hd hh hb hb' => ?_⟩
  have h1 : torusSiteInFrame (torusFrame L 0 m) (torusFrame L 0 m).top q ∈ cellsOfSites (torusFrame L 0 m) X :=
    (TopLevelSites.torusSiteInFrame_mem_cellsOfSites_iff hn).mpr hq
  have h2 : cellSupDist (torusSiteInFrame (torusFrame L 0 m) (torusFrame L 0 m).top q)
      (torusSiteInFrame (torusFrame L 0 m) (torusFrame L 0 m).top z) ≤ 2047 := by
    rw [cellSupDist_torusFrame, siteOfCell_torusSiteInFrame, siteOfCell_torusSiteInFrame]
    omega
  have h3 := hr _ h1 h2 hh hb fun i => (hb' i).trans (by norm_num)
  rw [TopLevelSites.mem_cellsOfSites_iff hn, toTorusSite_add (period_top_of_extent hn),
    toTorusSite_torusSiteInFrame (period_top_of_extent hn), toTorusSite_siteOfCoords (period_top_of_extent hn)] at h3
  exact h3
theorem isRegularRegion_coolRegion (hc : ComplementOfThickenedLumpsRegular) (hfit : R.params.Admissible)
    (s : ChartSetting R n) : IsRegularRegion s.coolRegion 1024 :=
  isRegularRegion_of_torusFrame R.params.side _
    (isOrthantRegular_cellsOfSites_compl_thickening hc hfit (Dvd.intro_left n rfl) (fun _ => rfl) s.fine)
theorem isRegularRegion_sitesUnderRegion (hfit : R.params.Admissible) (s : ChartSetting R n) {F : BlockFrame}
    (hnF : ∀ i, F.extent i = n) (h : IsOrthantRegular (cellsOfSites F s.region) 2047) :
    IsRegularRegion s.sitesUnderRegion 1024 := by
  classical
  have hL := hfit.L_odd
  have hL16 := hfit.L_ge
  have hLpos : (0 : ℤ) < R.params.side := by
    have : 0 < R.params.side := by omega
    exact_mod_cast this
  intro z
  obtain ⟨eps, he, hr⟩ := h (torusSiteInFrame F F.top (parentBlock R.params.side z))
  refine ⟨eps, he, fun q hq hd hh hb hb' => ?_⟩
  have hq' : parentBlock R.params.side q ∈ s.region := (Finset.mem_filter.mp hq).2
  obtain ⟨o, ho, hqe⟩ := exists_eq_blockCentreSite_add hL q
  set B := parentBlock R.params.side q with hB
  set c : ℤ := ((R.params.side : ℤ) - 1) / 2 with hc
  set δ : Fin 4 → ℤ := fun i => (o i + hh i + c) / (R.params.side : ℤ) with hδ
  have hblock : parentBlock R.params.side (q + siteOfInt hh) = B + siteOfInt δ := by
    have e : q + siteOfInt hh = blockCentreSite R.params.side B + siteOfInt (o + hh) := by
      rw [siteOfInt_add, ← add_assoc, ← hqe]
    rw [e, parentBlock_blockCentreSite_add]
    rfl
  have hmem : torusSiteInFrame F F.top B ∈ cellsOfSites F s.region :=
    (TopLevelSites.torusSiteInFrame_mem_cellsOfSites_iff hnF).mpr hq'
  have : ∀ i, NeZero (F.period F.top i) := fun i => period_neZero (period_top_of_extent hnF) i
  have hdist : cellSupDist (torusSiteInFrame F F.top B)
      (torusSiteInFrame F F.top (parentBlock R.params.side z)) ≤ 2047 := by
    have h1 : supDist B (parentBlock R.params.side z) ≤ supDist q z + 1 := supDist_parentBlock_le hL q z
    rw [TorusChain.cellSupDist_torusSiteInFrame (period_top_of_extent hnF)]
    omega
  have hsgn : ∀ i, 0 ≤ eps i * δ i ∧ |δ i| ≤ 2047 := by
    intro i
    have h1 := ho i
    have h2 := hb i
    have h3 := hb' i
    rw [Int.abs_eq_natAbs] at h3
    have hv : o i + hh i + c = (o i + c) + hh i := by ring
    have hδi : δ i = ((o i + c) + hh i) / (R.params.side : ℤ) := by
      simp only [hδ]
      rw [hv]
    have hlow : -1 ≤ δ i := by
      rw [hδi, Int.le_ediv_iff_mul_le hLpos]
      omega
    have hupp : δ i ≤ 1 := by
      have : δ i < 2 := by
        rw [hδi, Int.ediv_lt_iff_lt_mul hLpos]
        omega
      omega
    refine ⟨?_, by rw [abs_le]; omega⟩
    rcases he i with h4 | h4
    · rw [h4] at h2 ⊢
      have h5 : 0 ≤ hh i := by omega
      have : 0 ≤ δ i := by
        rw [hδi]
        exact Int.ediv_nonneg (by omega) hLpos.le
      omega
    · rw [h4] at h2 ⊢
      have h5 : hh i ≤ 0 := by omega
      have : δ i < 1 := by
        rw [hδi, Int.ediv_lt_iff_lt_mul hLpos]
        omega
      omega
  have hfin := hr _ hmem hdist δ (fun i => (hsgn i).1) fun i => (hsgn i).2
  rw [TopLevelSites.mem_cellsOfSites_iff hnF, toTorusSite_add (period_top_of_extent hnF),
    toTorusSite_torusSiteInFrame (period_top_of_extent hnF),
    toTorusSite_siteOfCoords (period_top_of_extent hnF)] at hfin
  unfold StepSettings.ChartSetting.sitesUnderRegion sitesInBlocks
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hblock ▸ hfin⟩
theorem isColdOn_coolRegion (hfit : R.params.Admissible) {σA : ℝ} (hσ : R.params.threshold ≤ σA)
    (s : ChartSetting R n) {W : TorusField (n * R.params.side)}
    (hW : torusHotSites R.params W = torusHotSites R.params s.fine) : IsColdOn σA s.coolRegion W := by
  intro p hp
  obtain ⟨hlt, hc⟩ := mem_plaquettesIn.mp hp
  by_contra hcon
  have hge : R.params.threshold ≤ curvature W p.1 p.2.1 p.2.2 := hσ.trans (not_lt.mp hcon)
  have hz := mem_torusHotSites_of_mem_plaquetteVertices hfit (Dvd.intro_left n rfl) hlt hge
    (base_mem_plaquetteVertices p.1 p.2.1 p.2.2)
  rw [hW] at hz
  have h1 := hc p.1 (base_mem_plaquetteVertices p.1 p.2.1 p.2.2)
  exact (Finset.mem_sdiff.mp h1).2
    ((mem_thickening _ _ _).mpr ⟨_, hz, by rw [supDist_self]; exact Nat.zero_le _⟩)
theorem isColdOn_gaugeTransform {m : ℕ} [NeZero m] {σA : ℝ} {X : Finset (TorusSite m)} {W : TorusField m}
    (h : IsColdOn σA X W) (g : TorusSite m → UnitQuaternion) : IsColdOn σA X (gaugeTransform g W) :=
  fun p hp => by
  rw [curvature_gaugeTransform]
  exact h p hp
section Sum
theorem sum_count_cast {m : ℕ} [NeZero m] (l : List (TorusSite m)) :
    ∑ y : TorusSite m, ((l.count y : ℕ) : ℝ) = l.length := by
  classical
  induction l with
  | nil => simp
  | cons b r ih =>
    simp only [List.count_cons, Nat.cast_add, Finset.sum_add_distrib, ih, List.length_cons, Nat.cast_succ]
    congr 1
    simp
theorem sum_levelShare_zero {m : ℕ} [NeZero m] (a : ℝ) (L : ℕ) (X : Finset (TorusSite m)) (W : TorusField m) :
    ∑ y, levelShare a L 0 X y W = actionAtLevel a L 0 X W := by
  show ∑ y : TorusSite m, ∑ p ∈ plaquettesIn X, (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) / 4 *
    plaquetteEnergy W p.1 p.2.1 p.2.2 = wilsonAction X W
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_div, sum_count_cast]
  simp [plaquetteVertices]
theorem sum_levelShare (hS : SharesSumToAction) {m : ℕ} [NeZero m] {a : ℝ} (ha : 0 ≤ a) {L : ℕ} (hL : 0 < L)
    (hm : 2 ≤ m) (t : ℕ) (X : Finset (TorusSite m)) (W : TorusField m) :
    ∑ y, levelShare a L t X y W = actionAtLevel a L t X W := by
  cases t with
  | zero => exact sum_levelShare_zero a L X W
  | succ t => exact hS a L t m X W ha hL hm
theorem sum_sitesInBlocks_singleton {L : ℕ} [NeZero L] (f : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ y, f y := by
  classical
  have h : ∀ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, f y =
      ∑ y ∈ Finset.univ.filter fun y => parentBlock L y = Y, f y := by
    intro Y
    unfold sitesInBlocks
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp
  simp only [h]
  exact Finset.sum_fiberwise _ _ _
theorem sum_bond_ends (g : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, ∑ i : Fin 4, (g (Y, i) + g (Y - TorusFields.unitStep n i, i)) = 2 * ∑ c : TorusBond n, g c := by
  simp only [Finset.sum_add_distrib]
  rw [Fintype.sum_prod_type]
  have h : ∑ Y : TorusSite n, ∑ i : Fin 4, g (Y - TorusFields.unitStep n i, i) = ∑ Y : TorusSite n, ∑ i : Fin 4, g (Y, i) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Fintype.sum_equiv (Equiv.subRight (TorusFields.unitStep n i)) _ _ fun Y => rfl
  rw [h]
  ring
end Sum
end FreeBonds
theorem StepSettings.ChartSetting.costSum_eq (hS : SharesSumToAction) (hfit : R.params.Admissible) (h2 : 2 ≤ n)
    (s : ChartSetting R n) (η : FreeCoords s.free)
    (hη : torusHotSites R.params (s.field η) = torusHotSites R.params s.fine) :
    s.costSum η = actionAtLevel R.params.coupling R.params.side R.depth s.coolRegion (s.field η) +
      R.params.coupling * ∑ c : TorusBond n, bondFit R.params (s.field η) s.coarse s.bases c := by
  have hLpos : 0 < R.params.side := hfit.L_odd.pos
  have hm : 2 ≤ n * R.params.side := by nlinarith
  have ha : 0 ≤ R.params.coupling := by linarith [hfit.a_ge]
  unfold StepSettings.ChartSetting.costSum blockCost
  rw [Finset.sum_add_distrib, FreeBonds.sum_sitesInBlocks_singleton, ← Finset.mul_sum, FreeBonds.sum_bond_ends, hη]
  have e := FreeBonds.sum_levelShare hS ha hLpos hm R.depth s.coolRegion (s.field η)
  unfold StepSettings.ChartSetting.coolRegion at e ⊢
  rw [e]
  ring
end YangMills.Construction
end
