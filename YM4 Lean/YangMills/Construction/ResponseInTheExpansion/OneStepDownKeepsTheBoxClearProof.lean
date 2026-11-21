import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAGround
import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBoundedProof
import YangMills.Construction.ResponseInTheExpansion.OneStepDownKeepsTheBoxClear
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepSettings YangMills.Construction.StepMarks YangMills.Construction.WeightedResponses MeasureTheory
section OneStep
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem parentBlock_mem_coreBlocks {L : ℕ} [NeZero L] (r : ℕ) {θ : Finset (TorusSite (n * L))}
    {z : TorusSite (n * L)} (hz : z ∈ θ) :
    parentBlock L z ∈ coreBlocks L r θ := by apply _root_.YangMills.Construction.BlockZones.parentBlock_mem_coreBlocks <;> assumption
private theorem parentBlock_not_mem_of_disjoint (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (C Z : Finset (TorusSite n))
    (hY : Disjoint (coarseHull R.params.side R.range R.nextRange bad Yt C) Z) (hF : FreeCoresAvoid R Yt bad C Z)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ bad.image Prod.fst ∪ Yt ∪ sitesInBlocks R.params.side C) :
    parentBlock R.params.side z ∉ Z := by
  classical
  obtain ⟨X, hX, hzX⟩ := exists_mem_chainComponents (r := 10 * R.range) hz
  intro hin
  by_cases hatt : (X ∩ sitesInBlocks R.params.side C).Nonempty
  · have hat : z ∈ attachedSites R.params.side R.range bad Yt C :=
      Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hatt⟩, hzX⟩
    have hst : parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad Yt C :=
      Finset.mem_union_right _ (parentBlock_mem_coreBlocks _ hat)
    exact Finset.disjoint_left.mp hY (subset_thickening_self _ _ hst) hin
  · exact Finset.disjoint_left.mp (hF X hX hatt) (parentBlock_mem_coreBlocks _ hzX) hin
abbrev _root_.YangMills.SharedProofs.p27757 := @parentBlock_not_mem_of_disjoint
private theorem isColdOnBall_of_disjoint (hfit : R.params.Admissible) (hLn : R.params.side ∣ n) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (o : TorusSite n)
    (m : ℝ)
    (hY : Disjoint (coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V)) (supBall o m)) :
    IsColdOnBall R.params.threshold V o m := by
  classical
  intro p hp
  by_contra hcon
  obtain ⟨hlt, hvert⟩ := (Finset.mem_filter.mp hp).2
  have hx : p.1 ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by simp [plaquetteVertices]
  have hl : torusLumpOf R.params p.1 ∈ torusHotLumps R.params V :=
    (mem_torusHotLumps_iff R.params hfit hLn V _).mpr ⟨p.1, p.2.1, p.2.2, hlt, not_lt.mp hcon, p.1, hx, rfl⟩
  have hs : p.1 ∈ torusHotSites R.params V := Finset.mem_biUnion.mpr ⟨_, hl, mem_torusLumpOf_self _⟩
  have hC : p.1 ∈ hotCoreSites R V := subset_thickening_self _ _ hs
  have hZ : p.1 ∈ storedBlocks R.params.side R.range bad Yt (hotCoreSites R V) := Finset.mem_union_left _ hC
  exact Finset.disjoint_left.mp hY (subset_thickening_self _ _ hZ) (hvert _ hx)
private theorem frameDeviation_lt_of_markLaw_ne_zero (hLn : R.params.side ∣ n) (h64 : 64 ≤ n) {V : TorusField n}
    {W : TorusField (n * R.params.side)} {bad : Finset (TorusBond (n * R.params.side))} (hc : markLaw R W V bad ≠ 0)
    {b : TorusBond (n * R.params.side)} (hb : b ∈ markedBonds R (hotCoreSites R V)) (hbad : b ∉ bad) :
    ‖(frameDeviation R.params R.anchorRadius R.depth R.frameReach V W b : Quaternion ℝ)‖ < R.params.threshold / 64 := by
  classical
  unfold markLaw at hc
  rw [if_pos ⟨hLn, h64⟩] at hc
  rw [if_pos (by by_contra h; exact hc (if_neg h))] at hc
  have h1 := Finset.prod_ne_zero_iff.mp hc b hb
  rw [if_neg hbad] at h1
  unfold StepSettings.bondMark ColdStepAtMirrorFrames.cutoffFactor at h1
  by_contra h2
  refine h1 (if_neg ?_)
  simpa [frameDeviation, StepSetup.ballRadius] using h2
end OneStep
section Chain
variable {ℓ : TorusLumps.StepParameters}
private theorem stage_depth_eq (T : StageTower ℓ) (h : T.base.depth = 0) : ∀ t, (T.stage t).depth = t
  | 0 => h
  | t + 1 => congrArg (· + 1) (stage_depth_eq T h t)
private theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private theorem ae_markLaw_ne_zero (T : StageTower ℓ) (hT : T.MarksMeasurable) (β : ℝ) (s n : ℕ) [NeZero n] :
    ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n),
      markLaw (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.2.2 ≠ 0 := by
  classical
  let _ := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
  let S : Set (MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n) :=
    {u | markLaw (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.2.2 = 0}
  have hS : MeasurableSet S := by
    have : Countable (BondSet (n * ℓ.side)) := inferInstanceAs (Countable (Finset (TorusBond (n * ℓ.side))))
    have hpair : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ((topField ℓ s (n * ℓ.side) u.1, u.2.2.1) : TorusField (n * ℓ.side) × TorusField n) :=
      ((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
    have hbad : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hU : S = ⋃ bad : BondSet (n * ℓ.side),
        ((fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.2) ⁻¹' {bad}) ∩
        ((fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
          ((topField ℓ s (n * ℓ.side) u.1, u.2.2.1) : TorusField (n * ℓ.side) × TorusField n)) ⁻¹'
            {p | markLaw (T.stage s).toStepSetup p.1 p.2 bad = 0}) := by
      ext u
      simp only [S, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        exists_eq_left']
    rw [hU]
    refine MeasurableSet.iUnion fun bad => (hbad (MeasurableSpace.measurableSet_top)).inter (hpair ?_)
    exact (hT s n bad) (measurableSet_singleton 0)
  rw [ae_iff]
  have hset : {u : MarkedSample ℓ (s + 1) n |
      ¬ markLaw (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.2.2 ≠ 0} = S := by
    ext u
    exact not_not
  rw [hset]
  show (((markedSampleLaw T β s (n * ℓ.side)).prod (stepReferenceMeasure ℓ n)).withDensity fun u =>
      ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2)) S = 0
  rw [withDensity_apply _ hS]
  have hz : ∀ u ∈ S,
      ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2) = 0 := by
    intro u hu
    have hu' : markLaw (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.2.2 = 0 := hu
    simp [stepOutcomeDensity, hu']
  rw [setLIntegral_congr_fun hS hz]
  simp
end Chain
private theorem two_le_floor_rpow {x : ℝ} (hx : (2 : ℝ) ^ 20 ≤ x) : 2 ≤ ⌊x ^ ((1 : ℝ) / 20)⌋₊ := by
  apply Nat.le_floor
  have h2 : (2 : ℝ) = ((2 : ℝ) ^ 20) ^ ((1 : ℝ) / 20) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  calc ((2 : ℕ) : ℝ) = 2 := by norm_num
    _ = ((2 : ℝ) ^ 20) ^ ((1 : ℝ) / 20) := h2
    _ ≤ x ^ ((1 : ℝ) / 20) := Real.rpow_le_rpow (by positivity) hx (by norm_num)
private theorem parentBlock_mem_supBall {n : ℕ} [NeZero n] {L : ℕ} [NeZero L] (hL : 2 ≤ L) {m : ℕ} (hm : 2 ≤ m)
    {z o' : TorusSite (n * L)} (hz : z ∈ supBall o' (m : ℝ)) :
    parentBlock L z ∈ supBall (parentBlock L o') (m : ℝ) := by
  classical
  have h1 : supDist z o' ≤ m := by
    have := (Finset.mem_filter.mp hz).2
    exact_mod_cast this
  have h2 := TorusBalls.supDist_parentBlock_le_div_add_one L z o'
  have h3 : supDist z o' / L ≤ m / 2 :=
    (Nat.div_le_div_right h1).trans (Nat.div_le_div_left hL (by norm_num))
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have h4 : supDist (parentBlock L z) (parentBlock L o') ≤ m := by omega
  exact_mod_cast h4
theorem descentKeepsBallClear : descentKeepsBallClearStatement := by
  intro a _
  refine ⟨64, fun _ => 1, 0, fun _ => one_pos, fun L _ hL Tb _ hTL hD _ _ _ _ => ⟨Tb.floorMin, fun y hy _ _ => ?_⟩⟩
  have hfit := hD.fits y hy
  refine ⟨2 ^ 20, ?_⟩
  intro T β k n _ nn j o hc hLn _
  have h64 : 64 ≤ n := by
    have h1 : (Tb.stepParameters y).side ≤ n := Nat.le_of_dvd (NeZero.pos n) hLn
    have h2 : (Tb.stepParameters y).side = L := hTL
    omega
  have hnum := stage_depth_eq T hc.onFamily.startsAtWilson.depth_eq (k + j)
  have hm : 2 ≤ localBlockSide (Tb.stepParameters y) β k := two_le_floor_rpow hc.floor_le
  filter_upwards [ae_markLaw_ne_zero T hc.measurable β (k + j) n] with u hmark hY
  let R := (T.stage (k + j)).toStepSetup
  have hYR : Disjoint (coarseHull R.params.side R.range R.nextRange u.2.2.2
      (stageState T (k + j) (n * R.params.side) u.1).2.1 (hotCoreSites R u.2.2.1))
      (supBall o (localBlockSide (Tb.stepParameters y) β k)) := hY
  refine ⟨isColdOnBall_of_disjoint R hfit hLn u.2.2.1 _ _ o _ hYR, fun hF => ?_⟩
  have hFR : FreeCoresAvoid R (stageState T (k + j) (n * R.params.side) u.1).2.1 u.2.2.2 (hotCoreSites R u.2.2.1)
      (supBall o (localBlockSide (Tb.stepParameters y) β k)) := hF
  refine ⟨fun o' ho' => ?_, fun b hb => ?_⟩
  · refine Finset.disjoint_left.mpr fun z hzY hzB => ?_
    have hz : z ∈ u.2.2.2.image Prod.fst ∪ (stageState T (k + j) (n * R.params.side) u.1).2.1 ∪
        sitesInBlocks R.params.side (hotCoreSites R u.2.2.1) :=
      Finset.mem_union_left _ (Finset.mem_union_right _ hzY)
    refine parentBlock_not_mem_of_disjoint R _ _ _ _ hYR hFR hz ?_
    have := parentBlock_mem_supBall T.two_le_side hm hzB
    rwa [ho'] at this
  · obtain ⟨hbc, hbB⟩ := Finset.mem_filter.mp hb
    have hnotbad : b ∉ (show Finset (TorusBond (n * (Tb.stepParameters y).side)) from u.2.2.2) := by
      intro hbad
      have hz : b.1 ∈ u.2.2.2.image Prod.fst ∪ (stageState T (k + j) (n * R.params.side) u.1).2.1 ∪
          sitesInBlocks R.params.side (hotCoreSites R u.2.2.1) :=
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hbad))
      exact parentBlock_not_mem_of_disjoint R _ _ _ _ hYR hFR hz hbB
    refine ⟨hnotbad, ?_⟩
    have hoff : parentBlock R.params.side b.1 ∉ hotCoreSites R u.2.2.1 := fun hin =>
      Finset.disjoint_left.mp hYR (subset_thickening_self _ _ (Finset.mem_union_left _ hin)) hbB
    have hmk : b ∈ markedBonds R (hotCoreSites R u.2.2.1) := Finset.mem_filter.mpr ⟨hbc, hoff⟩
    have := frameDeviation_lt_of_markLaw_ne_zero R hLn h64 hmark hmk hnotbad
    rw [show R.depth = k + j from hnum] at this
    exact this
end YangMills.Construction.ResponseInTheExpansion
end
