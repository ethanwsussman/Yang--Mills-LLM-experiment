import YangMills.Construction.ClusterExpansionOfAStep.GaugeOfACaseProof
import YangMills.Construction.ClusterExpansionOfAStep.GasesEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsAGas
import YangMills.Construction.ClusterExpansionOfAStep.RatiosOfXi
import YangMills.Construction.ResponseInTheExpansion.AQuietSettingAgreesWithItsMirror
import YangMills.Construction.ResponseInTheExpansion.ASettingOffABoxIsTheMirror
import YangMills.Construction.ResponseInTheExpansion.BoundedFunctionsOfTheCasesAreIntegrable
import YangMills.Construction.ResponseInTheExpansion.CaseMeanIsAMeanOfTheGas
import YangMills.Construction.ResponseInTheExpansion.FarSpinsMoveAVariableProof
import YangMills.Construction.ResponseInTheExpansion.FluctuationsOfAStepAreBorelProof
import YangMills.Construction.ResponseInTheExpansion.TheCasesOffABoxAreTheMirror
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepSettings StepGas StepCosts ClusterExpansionOfAStep
namespace CasesAwayFromBall
section Gauge
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem torusSiteInFrame_blockSite_centre (y : TorusSite n) :
    torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite (L := R.params.side) y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) = BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.torusSiteInFrame_blockSite_centre <;> assumption
private theorem axialGauge_gaugeTransform (hodd : Odd R.params.side)
    (Wf : (stepBlockFrame R.params.side n).GaugeField (stepBlockFrame R.params.side n).depth)
    (γ : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth → BlockAverages.UnitQuaternion)
    (x : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth) :
    LumpContours.axialGauge 1 (BlockAverages.gaugeTransform γ Wf) x =
      γ (BlockAverages.cellCentre (stepBlockFrame R.params.side n).depth (BlockAverages.enclosingCell x)) *
        LumpContours.axialGauge 1 Wf x * (γ x)⁻¹ := by
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨ho, hxe⟩ := GaugeFixing.cellOffset_mem_and_eq hs hodd x
  unfold LumpContours.axialGauge
  rw [GaugeFixing.pathHolonomy_gaugeTransform, GaugeFixing.pathDisplacement_axisPath, hxe]
abbrev _root_.YangMills.SharedProofs.p40454 := @axialGauge_gaugeTransform
private theorem blockGauge_gaugeTransform (hodd : Odd R.params.side)
    (u : TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion)
    (hc : ∀ y : TorusSite n, u (blockSite y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) = 1) (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) :
    BlockTrees.blockGauge R.params.side (TorusFields.gaugeTransform u W) x =
      BlockTrees.blockGauge R.params.side W x * (u x)⁻¹ := by
  have hp0 : ∀ k, (stepBlockFrame R.params.side n).period 0 k = n * R.params.side := fun k => BlockTrees.stepBlockFrame_period_zero k
  have hp1 : ∀ k, (stepBlockFrame R.params.side n).period 1 k = n := fun k => BlockTrees.stepBlockFrame_period_one k
  set X := torusSiteInFrame (stepBlockFrame R.params.side n) 0 x with hX
  have hread : readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform u W) =
      BlockAverages.gaugeTransform (fun z => u (toTorusSite (n * R.params.side) z))
        (readAtLevel (stepBlockFrame R.params.side n) 0 W) := SettingFits.readAtLevel_gaugeTransform hp0 u W
  have hcen : u (toTorusSite (n * R.params.side)
      (BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 (BlockAverages.enclosingCell X))) = 1 := by
    set y : TorusSite n := toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n (BlockAverages.enclosingCell X) with hy
    have e : torusSiteInFrame (stepBlockFrame R.params.side n) 1 y = BlockAverages.enclosingCell X :=
      TopLevelSites.toTorusSite_injective hp1 (TopLevelSites.toTorusSite_torusSiteInFrame hp1 y)
    have := torusSiteInFrame_blockSite_centre (R := R) y
    rw [e] at this
    rw [← this, TopLevelSites.toTorusSite_torusSiteInFrame hp0]
    exact hc y
  have e1 : BlockTrees.blockGauge R.params.side (TorusFields.gaugeTransform u W) x =
      LumpContours.axialGauge 1 (BlockAverages.gaugeTransform (fun z => u (toTorusSite (n * R.params.side) z))
        (readAtLevel (stepBlockFrame R.params.side n) 0 W)) X :=
    congrArg (fun Y => LumpContours.axialGauge 1 Y X) hread
  have e2 := axialGauge_gaugeTransform hodd (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    (fun z => u (toTorusSite (n * R.params.side) z)) X
  rw [e1, e2]
  show u (toTorusSite (n * R.params.side) (BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0
      (BlockAverages.enclosingCell X))) * BlockTrees.blockGauge R.params.side W x *
      (u (toTorusSite (n * R.params.side) X))⁻¹ = _
  rw [hcen, TopLevelSites.toTorusSite_torusSiteInFrame hp0, one_mul]
abbrev _root_.YangMills.DeltaSharedProofs.p501100 := @blockGauge_gaugeTransform
private theorem chartCoord_gaugeTransform (hodd : Odd R.params.side)
    (u : TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion)
    (hc : ∀ y : TorusSite n, u (blockSite y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) = 1) (V : TorusField n) (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    chartCoord R.params V (TorusFields.gaugeTransform u W) b = chartCoord R.params V W b := by
  classical
  have e : BlockTrees.blockGauge R.params.side (TorusFields.gaugeTransform u W) b.1 * TorusFields.gaugeTransform u W b.1 b.2 *
      (BlockTrees.blockGauge R.params.side (TorusFields.gaugeTransform u W) (b.1 + unitStep (n * R.params.side) b.2))⁻¹ =
      BlockTrees.blockGauge R.params.side W b.1 * W b.1 b.2 *
        (BlockTrees.blockGauge R.params.side W (b.1 + unitStep (n * R.params.side) b.2))⁻¹ := by
    rw [blockGauge_gaugeTransform hodd u hc, blockGauge_gaugeTransform hodd u hc]
    unfold TorusFields.gaugeTransform
    group
  rw [BlockTrees.chartCoord_eq, BlockTrees.chartCoord_eq, e]
abbrev _root_.YangMills.DeltaSharedProofs.p502171 := @chartCoord_gaugeTransform
end Gauge
section Means
private theorem abs_ratio_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {d G : α → ℝ} {B : ℝ} (hd : ∀ a, 0 ≤ d a)
    (hG : ∀ a, |G a| ≤ B) (hB : 0 ≤ B) : |(∫ a, G a * d a ∂μ) / ∫ a, d a ∂μ| ≤ B := by
  by_cases hi : Integrable d μ
  · have h1 : ‖∫ a, G a * d a ∂μ‖ ≤ ∫ a, B * d a ∂μ :=
      norm_integral_le_of_norm_le (hi.const_mul B) (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd a)]
        exact mul_le_mul_of_nonneg_right (hG a) (hd a))
    rw [integral_const_mul, Real.norm_eq_abs] at h1
    have h0 : 0 ≤ ∫ a, d a ∂μ := integral_nonneg hd
    rcases h0.eq_or_lt with h | h
    · rw [← h]
      simpa using hB
    · rw [abs_div, abs_of_pos h, div_le_iff₀ h]
      exact h1
  · rw [integral_undef hi]
    simpa using hB
abbrev _root_.YangMills.SharedProofs.p11634 := @abs_ratio_le
private theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ ColdStepAtMirrorFrames.cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem chartDensity_nonneg (s : ChartSetting R n) (η : FreeCoords s.free) : 0 ≤ WeightedResponses.chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_nonneg <;> assumption
private theorem imaginaryComponent_sub (e : Fin 3) (a b : BlockAverages.imaginaryQuaternions) :
    BlockAverages.imaginaryComponent e (a - b) = BlockAverages.imaginaryComponent e a - BlockAverages.imaginaryComponent e b := by
  fin_cases e <;> simp [BlockAverages.imaginaryComponent]
end Means
section Quiet
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem exists_state_of_occupies {G : GasGround R n} {σ : G.Config} {θ : GasSupport R n} (h : (G.familyOf σ).Occupies θ) :
    ∃ hs : G.IsGasSupport θ, σ ⟨θ, hs⟩ ≠ Sum.inl () := by
  classical
  unfold GasFamily.Occupies GasGround.familyOf at h
  by_cases hs : G.IsGasSupport θ
  · refine ⟨hs, fun h0 => ?_⟩
    simp [dif_pos hs, h0] at h
  · simp [dif_neg hs] at h
private theorem parentBlock_not_mem_of_quiet {G : GasGround R n} {σ : G.Config} {A : Finset (TorusSite n)}
    (hσ : ∀ Y ∈ A, σ ∈ G.NoSpinMeets Y) {θ : GasSupport R n} (h : (G.familyOf σ).Occupies θ)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites) : parentBlock R.params.side z ∉ A := by
  intro hA
  obtain ⟨hs, hne⟩ := exists_state_of_occupies h
  refine hne (hσ _ hA ⟨θ, hs⟩ ?_)
  rcases Finset.mem_union.mp hz with h1 | h1
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h1
    exact Or.inl ⟨c, hc, rfl⟩
  · exact Or.inr ⟨z, h1, rfl⟩
abbrev _root_.YangMills.SharedProofs.p26926 := @parentBlock_not_mem_of_quiet
private theorem mem_sitesInBlocks {L : ℕ} [NeZero L] {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
private theorem parentBlock_mem_blocksNearFreeCores {Q : Finset (TorusSite n)} {v z : TorusSite (n * R.params.side)}
    (hv : parentBlock R.params.side v ∈ Q) (h : supDist v z ≤ 4 * R.range) :
    parentBlock R.params.side z ∈ blocksNearFreeCores R.params.side R.range Q :=
  Finset.mem_image.mpr ⟨z, (mem_thickening _ _ _).mpr ⟨v, mem_sitesInBlocks.mpr hv, by rw [supDist_comm]; exact h⟩, rfl⟩
private theorem core_disjoint_of_quiet {G : GasGround R n} {σ : G.Config} {Q : Finset (TorusSite n)}
    (hσ : ∀ Y ∈ blocksNearFreeCores R.params.side R.range Q, σ ∈ G.NoSpinMeets Y) {θ : GasSupport R n}
    (h : (G.familyOf σ).Occupies θ) : Disjoint θ.core Q := by
  refine Finset.disjoint_left.mpr fun y hy hyQ => ?_
  obtain ⟨p, hp, z, hz, hpz⟩ := GasSupport.mem_core.mp hy
  exact parentBlock_not_mem_of_quiet hσ h hz (parentBlock_mem_blocksNearFreeCores (hp ▸ hyQ) hpz)
set_option maxHeartbeats 1000000 in
private theorem freeCoresAvoid_of_quiet (hfit : R.params.Admissible) (hr : 2 ^ 16 ≤ R.nextRange)
    (hrr : R.range ≤ R.nextRange + 1) {V : TorusField n} {q : CoarseState R n}
    (hot : (hotCaseGround R V q).IsHotCase) {σ : (hotCaseGround R V q).Config} {Q : Finset (TorusSite n)}
    (hσ : ∀ Y ∈ blocksNearFreeCores R.params.side R.range Q, σ ∈ (hotCaseGround R V q).NoSpinMeets Y) (hdis : Disjoint q.1 Q) :
    FreeCoresAvoid R (WeightedResponses.configSetting (hotCaseGround R V q) σ).support
      ((hotCaseGround R V q).badBondsOf σ) (hotCoreSites R V) Q := by
  classical
  intro X hX hfree
  refine Finset.disjoint_left.mpr fun y hyc hyQ => ?_
  obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hyc).2
  obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
  obtain ⟨z, hz, hvz⟩ := (mem_thickening _ _ _).mp hv2
  have hvb : parentBlock R.params.side v = y := Finset.mem_singleton.mp (mem_sitesInBlocks.mp hv1)
  have hzA : parentBlock R.params.side z ∈ blocksNearFreeCores R.params.side R.range Q :=
    parentBlock_mem_blocksNearFreeCores (hvb ▸ hyQ) hvz
  have hstored : ¬ ∃ s, q.markAt (parentBlock R.params.side z) = some s := by
    rintro ⟨s, hs⟩
    obtain ⟨W₀, Y₀, ω₀, bad₀, b₀, hst, -⟩ := hot.exists_state
    have hst' : coarseStateOf R (hotCoreSites R V) W₀ Y₀ ω₀ bad₀ b₀ = q := hst
    have hzs : parentBlock R.params.side z ∈ storedBlocks R.params.side R.range bad₀ Y₀ (hotCoreSites R V) := by
      by_contra hn
      have h0 := markAt_coarseStateOf (R := R) (hotCoreSites R V) W₀ Y₀ ω₀ bad₀ b₀ (parentBlock R.params.side z)
      rw [if_neg hn, hst', hs] at h0
      cases h0
    have hdist : supDist y (parentBlock R.params.side z) ≤ R.nextRange / 2 := by
      have hs1 := TorusBlocks.mul_supDist_parentBlock_le hfit.L_odd v z
      rw [hvb] at hs1
      have hL := hfit.L_ge
      set d := supDist y (parentBlock R.params.side z) with hd
      have h1 : supDist v z ≤ 4 * R.range := hvz
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · omega
      · obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        have h2 : R.params.side * e ≤ 4 * R.range := by
          rw [he, Nat.mul_add] at hs1
          omega
        have h3 : 2 ^ 16 * e ≤ R.params.side * e := Nat.mul_le_mul_right _ hL
        omega
    have hmem : y ∈ q.1 := by
      rw [← hst']
      exact (mem_thickening _ _ _).mpr ⟨_, hzs, hdist⟩
    exact Finset.disjoint_left.mp hdis hmem hyQ
  have hzS : z ∈ clusterSites (L := R.params.side) ((hotCaseGround R V q).badBondsOf σ)
      (WeightedResponses.configSetting (hotCaseGround R V q) σ).support (hotCoreSites R V) :=
    subset_of_mem_chainComponents hX hz
  rcases Finset.mem_union.mp hzS with h | h
  · rcases Finset.mem_union.mp h with h | h
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
      rcases Finset.mem_union.mp hc with h1 | h1
      · obtain ⟨s, hs, -⟩ := (Finset.mem_filter.mp h1).2
        exact hstored ⟨s, hs⟩
      · obtain ⟨θ, hθ, hcθ⟩ := Finset.mem_biUnion.mp h1
        exact parentBlock_not_mem_of_quiet hσ (Finset.mem_filter.mp hθ).2
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcθ)) hzA
    · rcases (BoxAgreement.mem_settingOf_support_iff (hotCaseGround R V q) ((hotCaseGround R V q).familyOf σ) z).mp h with h1 | h1
      · apply hstored
        have h1' : (match q.markAt (parentBlock R.params.side z) with
          | some s => s.siteLabel (siteOffset z)
          | none => Sum.inl ()).isRight = true := h1
        cases hs : q.markAt (parentBlock R.params.side z) with
        | none =>
          rw [hs] at h1'
          simp at h1'
        | some s => exact ⟨s, rfl⟩
      · obtain ⟨θ, hθ, hzθ⟩ := GasFamily.exists_of_mem_sites h1
        exact parentBlock_not_mem_of_quiet hσ hθ (Finset.mem_union_right _ hzθ) hzA
  · exact hfree ⟨z, Finset.mem_inter.mpr ⟨hz, h⟩⟩
end Quiet
section Case
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem abs_casesAwayFromBall_le (V : TorusField n) (Q : Finset (TorusSite n)) (Z : Finset (TorusBond (n * R.params.side)))
    (F : (↥Z × Fin 3 → ℝ) → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hFB : ∀ v, |F v| ≤ B) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) : |casesAwayFromBall R V Q Z F W Yt ωt bad b| ≤ B := by
  unfold casesAwayFromBall
  split_ifs
  · exact hFB _
  · simpa using hB0
private theorem measurable_imaginaryComponent {Ξ : Type} [MeasurableSpace Ξ] (f : Ξ → BlockAverages.imaginaryQuaternions)
    (h : MeasurableQuaternion fun ξ => ((f ξ : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) (e : Fin 3) :
    Measurable fun ξ => BlockAverages.imaginaryComponent e (f ξ) := by apply _root_.YangMills.SharedProofs.p32747 <;> assumption
private theorem measurable_frameDeviation (hBor : ChartCoordMeasurable) (V : TorusField n)
    (Z : Finset (TorusBond (n * R.params.side))) :
    Measurable fun W : TorusField (n * R.params.side) =>
      imaginaryComponentsOn Z (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V W) := by
  refine measurable_pi_lambda _ fun p => ?_
  obtain ⟨c, e⟩ := p
  show Measurable fun W : TorusField (n * R.params.side) =>
    BlockAverages.imaginaryComponent e (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V W c.1)
  simp only [StepMarks.frameDeviation, imaginaryComponent_sub]
  refine Measurable.sub ?_ measurable_const
  have hp : Measurable fun W : TorusField (n * R.params.side) => ((V, W) : TorusField n × TorusField (n * R.params.side)) :=
    measurable_const.prodMk measurable_id
  have h := (measurable_imaginaryComponent (fun r : TorusField n × TorusField (n * R.params.side) =>
    chartCoord R.params r.1 r.2 c.1) (hBor R.params n c.1) e).comp hp
  have e' : (fun W : TorusField (n * R.params.side) => BlockAverages.imaginaryComponent e (chartCoord R.params V W c.1)) =
      (fun r : TorusField n × TorusField (n * R.params.side) => BlockAverages.imaginaryComponent e (chartCoord R.params r.1 r.2 c.1)) ∘
        (fun W : TorusField (n * R.params.side) => ((V, W) : TorusField n × TorusField (n * R.params.side))) := by
    funext W
    simp only [Function.comp]
  rw [e']
  exact h
private theorem measurable_casesAwayFromBall (hBor : ChartCoordMeasurable) (V : TorusField n) (Q : Finset (TorusSite n))
    (Z : Finset (TorusBond (n * R.params.side))) {F : (↥Z × Fin 3 → ℝ) → ℝ} (hFm : Measurable F)
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => casesAwayFromBall R V Q Z F p.1 Yt p.2 bad b := by
  unfold casesAwayFromBall
  split_ifs
  · exact hFm.comp ((measurable_frameDeviation hBor V Z).comp measurable_fst)
  · exact measurable_const
private theorem casesAwayFromBall_gaugeInvariant (hodd : Odd R.params.side) (V : TorusField n) (Q : Finset (TorusSite n))
    (Z : Finset (TorusBond (n * R.params.side))) (F : (↥Z × Fin 3 → ℝ) → ℝ) :
    WeightedResponses.IsGaugeInvariantCase (casesAwayFromBall R V Q Z F) := by
  intro W Yt ωt bad b u _ _ hc
  have e : StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V (TorusFields.gaugeTransform u W) =
      StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V W := by
    funext c
    simp only [StepMarks.frameDeviation, chartCoord_gaugeTransform hodd u hc]
  unfold casesAwayFromBall
  rw [e]
private theorem weightedMean_casesAwayFromBall_of_quiet (hfit : R.params.Admissible) (hr : 2 ^ 16 ≤ R.nextRange)
    (hrr : R.range ≤ R.nextRange + 1) {V : TorusField n} {q : CoarseState R n}
    (hot : (hotCaseGround R V q).IsHotCase) {σ : (hotCaseGround R V q).Config} {Q : Finset (TorusSite n)}
    (hσ : ∀ Y ∈ blocksNearFreeCores R.params.side R.range Q, σ ∈ (hotCaseGround R V q).NoSpinMeets Y) (hdis : Disjoint q.1 Q)
    (Z : Finset (TorusBond (n * R.params.side))) (F : (↥Z × Fin 3 → ℝ) → ℝ) :
    (weightedMean (WeightedResponses.chartDensity (WeightedResponses.configSetting (hotCaseGround R V q) σ)) fun η =>
      casesAwayFromBall R V Q Z F ((WeightedResponses.configSetting (hotCaseGround R V q) σ).field η)
        (WeightedResponses.configSetting (hotCaseGround R V q) σ).support
        (WeightedResponses.configSetting (hotCaseGround R V q) σ).labelling ((hotCaseGround R V q).badBondsOf σ)
        (WeightedResponses.configSetting (hotCaseGround R V q) σ).bases) =
      weightedMean (WeightedResponses.chartDensity (WeightedResponses.configSetting (hotCaseGround R V q) σ)) fun η =>
        F (imaginaryComponentsOn Z (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V
          ((WeightedResponses.configSetting (hotCaseGround R V q) σ).field η))) := by
  have hm := freeCoresAvoid_of_quiet hfit hr hrr hot hσ hdis
  unfold casesAwayFromBall
  simp only [if_pos hm]
end Case
private theorem abs_integral_sub_le_of_rare {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : Integrable g P) {M ε B e : ℝ} (A : Finset ι) (N : ι → Set Ω) (hN : ∀ Y, MeasurableSet (N Y))
    (hp : ∀ Y ∈ A, 1 - e ≤ P.real (N Y)) (hgood : ∀ᵐ σ ∂P, (∀ Y ∈ A, σ ∈ N Y) → |g σ - M| ≤ ε)
    (hgB : ∀ᵐ σ ∂P, |g σ| ≤ B) (hMB : |M| ≤ B) (hε : 0 ≤ ε) (hB : 0 ≤ B) :
    |∫ σ, g σ ∂P - M| ≤ ε + 2 * B * A.card * e := by
  classical
  set H : Set Ω := ⋃ Y ∈ A, (N Y)ᶜ with hH
  have hHm : MeasurableSet H := Finset.measurableSet_biUnion _ fun Y _ => (hN Y).compl
  have hHp : P.real H ≤ A.card * e := by
    calc P.real H ≤ ∑ Y ∈ A, P.real (N Y)ᶜ := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ Y ∈ A, e := Finset.sum_le_sum fun Y hY => by
          rw [probReal_compl_eq_one_sub (hN Y)]
          linarith [hp Y hY]
      _ = A.card * e := by simp
  have hpt : ∀ᵐ σ ∂P, |g σ - M| ≤ ε + H.indicator (fun _ => 2 * B) σ := by
    filter_upwards [hgood, hgB] with σ h1 h2
    by_cases hσ : σ ∈ H
    · rw [Set.indicator_of_mem hσ]
      have := abs_sub (g σ) M
      linarith
    · rw [Set.indicator_of_notMem hσ]
      have : ∀ Y ∈ A, σ ∈ N Y := fun Y hY => by
        by_contra hc
        exact hσ (Set.mem_biUnion hY hc)
      linarith [h1 this]
  have hi2 : Integrable (H.indicator fun _ => 2 * B) P := (integrable_const _).indicator hHm
  calc |∫ σ, g σ ∂P - M| = |∫ σ, (g σ - M) ∂P| := by
        rw [integral_sub hg (integrable_const _)]
        simp
    _ ≤ ∫ σ, |g σ - M| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ σ, (ε + H.indicator (fun _ => 2 * B) σ) ∂P :=
        integral_mono_ae (hg.sub (integrable_const _)).abs ((integrable_const _).add hi2) hpt
    _ = ε + 2 * B * P.real H := by
        rw [integral_add (integrable_const _) hi2, integral_const, integral_indicator_const _ hHm]
        simp [mul_comm]
    _ ≤ ε + 2 * B * A.card * e := by
        have := mul_le_mul_of_nonneg_left hHp (by positivity : 0 ≤ 2 * B)
        linarith
abbrev _root_.YangMills.SharedProofs.p43034 := @abs_integral_sub_le_of_rare
end CasesAwayFromBall
open CasesAwayFromBall in
theorem casesAwayFromBallReflect_holds (hCM₀ : WeightedResponses.caseMeanEqGasMeanStatement)
    (hCol₀ : ClusterExpansionOfAStep.GasColumnsSmall) (hRat : ClusterExpansionOfAStep.PartitionRatioBounds)
    (hImg₀ : coarseStateGasStatement) (hGr₀ : HullStateIsHotCase)
    (hCfg₀ : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hQ : coldMirrorSettingAgreementStatement)
    (hS₀ : settingNearColdMirrorStatement) (hU : WeightedResponses.boundedCaseFunctionIntegrableStatement)
    (hBor : ChartCoordMeasurable) : casesAwayFromBallReflectStatement := by
  classical
  obtain ⟨r1, hr1, hCM⟩ := hCM₀
  obtain ⟨r2, hr2, hCol⟩ := hCol₀
  obtain ⟨r3, hr3, hImg⟩ := hImg₀
  obtain ⟨r4, hr4, hS⟩ := hS₀
  refine ⟨fun c => min (min (r1 c) (r2 c)) (min (r3 c) (r4 c)),
    fun c => lt_min (lt_min (hr1 c) (hr2 c)) (lt_min (hr3 c) (hr4 c)), fun T hT hC hrt => ?_⟩
  have hrt1 := hrt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrt2 := hrt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrt3 := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrt4 := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y1, h1⟩ := hCM T hT hrt1
  obtain ⟨y2, h2⟩ := hCol T hT hrt2
  obtain ⟨y3, h3⟩ := hImg T hT hrt3
  obtain ⟨y4, h4⟩ := hS T hT hC hrt4
  obtain ⟨y5, h5⟩ := hGr₀ T hT
  obtain ⟨y6, h6⟩ := hCfg₀ T hT
  refine ⟨max (max (max y1 y2) (max y3 y4)) (max y5 y6),
    fun y hy R hOn hF hx n m _ _ V q o hb hull hΦ hrm hmn hdis Z F B hZ hFm hFB => ?_⟩
  have e1 : y1 ≤ y := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hy
  have e2 : y2 ≤ y := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hy
  have e3 : y3 ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hy
  have e4 : y4 ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hy
  have e5 : y5 ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have e6 : y6 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have eL : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have eσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have en₀ : R.params.n₀ = T.n₀ := by rw [hOn.params_eq]; rfl
  have hfit := hF.admissible
  have hodd := hfit.L_odd
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hm₀def : R.frameReach = R.range / 2048 := rfl
  have hrb := hF.range_ge_side
  have hrf := hF.range_ge_base
  have hrg := hF.nextRange_ge
  have hra := hF.range_le
  have hn₀L : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hb.2
  have hrL : 2 ^ 40 ≤ R.range := by
    have : 2 ^ 40 * 1 ≤ 2 ^ 40 * R.params.side := Nat.mul_le_mul_left _ hLpos
    omega
  have hm₀pos : 0 < R.frameReach := by
    rw [hm₀def]
    omega
  have hm₀r : R.frameReach ≤ R.range := by
    rw [hm₀def]
    exact Nat.div_le_self _ _
  have hmr : 4096 * R.range ≤ m := by
    have : (2 : ℕ) ^ 12 = 4096 := by norm_num
    omega
  have hn2 : 2 ≤ n := by omega
  have hot := h5 y e5 R hOn hF n hb V q hull hΦ
  have hG : (hotCaseGround R V q).IsAdmissibleGround := Or.inr hot
  have cols := fun off => h2 y e2 R hOn hx n (hotCaseGround R V q) hG off
  obtain ⟨hNM, hxi, -, hratio, hbounds⟩ := hRat R n (hotCaseGround R V q) T.gasRate cols
  obtain ⟨-, -, -, hmass, -⟩ := h3 y e3 R hOn hx n (hotCaseGround R V q) hG
  have hpart : (hotCaseGround R V q).partitionFunction ∅ ≠ ⊤ := by
    intro ht
    have := hxi ∅
    unfold GasGround.xi at this
    rw [ht] at this
    simp at this
  have hfin : coarseStateMass R (hotCaseGround R V q).cut (hotCaseGround R V q).coarse (hotCaseGround R V q).state ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hpart
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB 0)
  have hint := hU R hF n hn₀L _ _ _ hfin (casesAwayFromBall R V (supBall o m) Z F) B
    (measurable_casesAwayFromBall hBor V _ Z hFm) (abs_casesAwayFromBall_le V _ Z F hB0 hFB)
  obtain ⟨hae, hcm⟩ := h1 y e1 R hOn hx n (hotCaseGround R V q) hG
  obtain ⟨hgi, hmean⟩ := hcm _ (measurable_casesAwayFromBall hBor V _ Z hFm) (casesAwayFromBall_gaugeInvariant hodd V _ Z F) hint
  obtain ⟨hw, hsc⟩ := cols fun j => j.1.Touches ∅
  have hprob : IsProbabilityMeasure ((hotCaseGround R V q).gibbsLaw ∅) := hsc.isProbabilityMeasure
  have hMB : |reflectedStepMean R m o V (fun k => F (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o k)))| ≤ B := by
    unfold reflectedStepMean ColdStepAtMirrorFrames.cutoffMean
    exact abs_ratio_le (fun a => mul_nonneg (Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _ _ _) (Real.exp_pos _).le)
      (fun a => hFB _) hB0
  have hZ' : ∀ b ∈ Z, b ∈ chartBonds R.params.side n ∧
      supDist (parentBlock R.params.side b.1) o ≤ (m - R.frameReach - 1) / 4 := by
    intro b hb'
    obtain ⟨h1', h2'⟩ := Finset.mem_filter.mp (hZ hb')
    refine ⟨h1', ?_⟩
    have h3' := (Finset.mem_filter.mp h2').2
    have h4' : 8 * supDist (parentBlock R.params.side b.1) o ≤ m := by
      have : (8 : ℝ) * (supDist (parentBlock R.params.side b.1) o : ℝ) ≤ m := by linarith
      exact_mod_cast this
    omega
  have hr' : (R.range : ℝ) / (4 * T.side) ≤ ((m - R.frameReach - 1 : ℕ) : ℝ) := by
    have hTL : (1 : ℝ) ≤ 4 * T.side := by
      rw [← eL]
      have : (1 : ℝ) ≤ R.params.side := by exact_mod_cast hLpos
      linarith
    have h5' : (R.range : ℝ) / (4 * T.side) ≤ R.range := div_le_self (Nat.cast_nonneg _) hTL
    have h6' : R.range ≤ m - R.frameReach - 1 := by omega
    have h7' : (R.range : ℝ) ≤ ((m - R.frameReach - 1 : ℕ) : ℝ) := by exact_mod_cast h6'
    linarith
  have hTn : T.n₀ ≤ n := en₀ ▸ hn₀L
  have hTm : T.n₀ ≤ 4 * m := by
    rw [← en₀]
    omega
  show |WeightedResponses.caseMean R (hotCaseGround R V q).cut (hotCaseGround R V q).coarse (hotCaseGround R V q).state
    (casesAwayFromBall R V (supBall o m) Z F) - _| ≤ _
  rw [hmean]
  unfold WeightedResponses.gasExpectationOfCase GasGround.expectation
  refine abs_integral_sub_le_of_rare hgi (blocksNearFreeCores R.params.side R.range (supBall o m))
    (hotCaseGround R V q).NoSpinMeets hNM (fun Y _ => ?_) ?_ ?_ hMB (by positivity) hB0
  · rw [hratio ∅ Y]
    exact (hbounds ∅ Y).1
  · filter_upwards [hae] with σ hσ' hσ
    rw [weightedMean_casesAwayFromBall_of_quiet hfit hrg hra hot hσ hdis Z F]
    have hset := h6 y e6 R hOn hx n (hotCaseGround R V q) hG σ hσ'.1
    obtain ⟨hcold, hagree⟩ := hQ R n m V q ((hotCaseGround R V q).familyOf σ) o hfit hn2 hb.1 (by omega) hm₀pos (by omega)
      (by omega) (by omega) hull hdis (fun θ hθ => core_disjoint_of_quiet hσ hθ)
    rw [eσ] at hcold
    exact h4 y e4 R hOn n m (m - R.frameReach - 1) (WeightedResponses.configSetting (hotCaseGround R V q) σ) o hTn hTm hset
      hcold hagree hr' Z F B hZ' hFm hFB
  · refine Filter.Eventually.of_forall fun σ => ?_
    unfold weightedMean
    exact abs_ratio_le (chartDensity_nonneg _) (fun η => abs_casesAwayFromBall_le V _ Z F hB0 hFB _ _ _ _ _) hB0
end YangMills.Construction.ResponseInTheExpansion
end
