import YangMills.Construction.ClusterExpansionOfAStep.GaugeOfACaseProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanScoresOverAStep
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportVariablesHaveTheirSizes
import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.TorusContours
open YangMills.Construction.StepSettings YangMills.Construction.StepCosts YangMills.Construction.StepGas
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.ColdStepAtMirrorFrames
namespace SupportResponseBound
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Gauges
private theorem fineRead_gauge (g : TorusSite (n * R.params.side) → UnitQuaternion) (W : TorusField (n * R.params.side)) :
    readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun x => g (toTorusSite (n * R.params.side) x)) (readAtLevel (stepBlockFrame R.params.side n) 0 W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.readAtLevel_zero_gaugeTransform <;> assumption
private theorem stepHotLumps_gauge (g : TorusSite (n * R.params.side) → UnitQuaternion) (W : TorusField (n * R.params.side)) :
    stepHotLumps R.params (TorusFields.gaugeTransform g W) = stepHotLumps R.params W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.stepHotLumps_gaugeTransform <;> assumption
private theorem contourMean_of_trivial_at_bases {F : BlockFrame} [∀ j i, NeZero (F.period j i)] (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (γ : F.Site F.depth → UnitQuaternion)
    (b : F.Cell → F.Site F.depth) (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) (h1 : γ (b c.1) = 1)
    (h2 : γ (b (c.1 + BlockAverages.unitStep F.top c.2)) = 1) : contourMean J₀ h b (BlockAverages.gaugeTransform γ W) c = contourMean J₀ h b W c := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.contourMean_gaugeTransform_of_eq_one <;> assumption
private theorem contourMean_gauge {u : TorusSite (n * R.params.side) → UnitQuaternion} (W : TorusField (n * R.params.side)) {b : BaseChoice R.params.side n}
    (hb : ∀ e, u (toTorusSite (n * R.params.side) (b e)) = 1) (c : (stepBlockFrame R.params.side n).Cell × Fin 4) :
    contourMean R.params.baseDepth (stepHotLumps R.params (TorusFields.gaugeTransform u W)) b (readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform u W)) c =
      contourMean R.params.baseDepth (stepHotLumps R.params W) b (readAtLevel (stepBlockFrame R.params.side n) 0 W) c := by
  rw [stepHotLumps_gauge, fineRead_gauge]
  exact contourMean_of_trivial_at_bases (F := stepBlockFrame R.params.side n) _ _ _ _ _ _ (hb _) (hb _)
abbrev _root_.YangMills.SharedProofs.p5543 := @contourMean_gauge
private theorem bondFit_gauge {u : TorusSite (n * R.params.side) → UnitQuaternion} (W : TorusField (n * R.params.side)) (V : TorusField n) {b : BaseChoice R.params.side n}
    (hb : ∀ e, u (toTorusSite (n * R.params.side) (b e)) = 1) (c : TorusBond n) :
    bondFit R.params (TorusFields.gaugeTransform u W) V b c = bondFit R.params W V b c := by
  have hm := contourMean_gauge W hb (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)
  exact congrArg (fun q : Quaternion ℝ => ‖q‖ - (q *
    ((readAtLevel (stepBlockFrame R.params.side n) 1 V (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1) c.2)⁻¹ : UnitQuaternion)).re) hm
private theorem bondKernelAt_gauge {u : TorusSite (n * R.params.side) → UnitQuaternion} (x : ℝ) (W : TorusField (n * R.params.side)) (V : TorusField n)
    {b : BaseChoice R.params.side n} (hb : ∀ e, u (toTorusSite (n * R.params.side) (b e)) = 1) (c : TorusBond n) :
    bondKernelAt R.params x (TorusFields.gaugeTransform u W) V b c = bondKernelAt R.params x W V b c := by
  have hm := contourMean_gauge W hb (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)
  unfold stepHotLumps at hm
  exact congrArg (fun q : Quaternion ℝ => Real.exp (R.params.coupling * x * (q *
    ((readAtLevel (stepBlockFrame R.params.side n) 1 V (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1) c.2)⁻¹ : UnitQuaternion)).re) / partitionFn (R.params.coupling * x * ‖q‖)) hm
private theorem bondScore_gauge {u : TorusSite (n * R.params.side) → UnitQuaternion} (x : ℝ) (W : TorusField (n * R.params.side)) (V : TorusField n)
    {b : BaseChoice R.params.side n} (hb : ∀ e, u (toTorusSite (n * R.params.side) (b e)) = 1) (c : TorusBond n) :
    bondScore R.params x (TorusFields.gaugeTransform u W) V b c = bondScore R.params x W V b c := by
  unfold bondScore fitConditionalMean
  simp only [bondFit_gauge _ _ hb, bondKernelAt_gauge _ _ _ hb]
private theorem blockBondScores_gauge {u : TorusSite (n * R.params.side) → UnitQuaternion} (W : TorusField (n * R.params.side)) (V : TorusField n)
    {b : BaseChoice R.params.side n} (hb : ∀ e, u (toTorusSite (n * R.params.side) (b e)) = 1) (Y : TorusSite n) :
    blockBondScores (R := R) (TorusFields.gaugeTransform u W) V b Y = blockBondScores (R := R) W V b Y := by
  unfold blockBondScores
  simp only [bondScore_gauge _ _ _ hb]
private theorem isHullState_gauge (hfit : R.params.Admissible) (g : TorusSite (n * R.params.side) → UnitQuaternion) (W : TorusField (n * R.params.side)) (r : ℕ)
    (Y : Finset (TorusSite (n * R.params.side))) : IsHullState R.params r (TorusFields.gaugeTransform g W) Y ↔ IsHullState R.params r W Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.isHullState_gaugeTransform_iff <;> assumption
private theorem isLiveState_gauge (hfit : R.params.Admissible) (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (u : TorusSite (n * R.params.side) → UnitQuaternion) {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    (h : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) : IsLiveState R.params R.coupling R.labelWeight (TorusFields.gaugeTransform u W) Yt (R.labels.act Yt u ωt) := by
  refine ⟨(isHullState_gauge hfit u W _ Yt).mpr h.1, ?_⟩
  rw [hrow.2.gauge _ hb W Yt ωt u h.1]
  exact h.2
private theorem supportResponseSum_gauge (A : ResponseSetup R) (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    (bad : Finset (TorusBond (n * R.params.side))) {b : BaseChoice R.params.side n} {u : TorusSite (n * R.params.side) → UnitQuaternion}
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) (hu : ∀ e, u (toTorusSite (n * R.params.side) (b e)) = 1) :
    supportResponseSum A V f (TorusFields.gaugeTransform u W) Yt (R.labels.act Yt u ωt) bad b = supportResponseSum A V f W Yt ωt bad b := by
  unfold supportResponseSum centeredHullResponse
  simp only [blockBondScores_gauge _ _ hu]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  exact congrArg (fun z => z - A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f) (hres.bounds.hull_gauge _ hb y u W Yt ωt hl f)
abbrev _root_.YangMills.SharedProofs.p54822 := @supportResponseSum_gauge
end Gauges
section Borel
private theorem measurableSet_isLiveState (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have hm := (hrow.2.borel _ hb Yt).1
  have e : {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} =
      (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0) ⁻¹' Set.Ioi 0 := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, IsLiveState]
    split_ifs with hh
    · simp [hh]
    · simp [hh]
  rw [e]
  convert hm measurableSet_Ioi using 3
abbrev _root_.YangMills.SharedProofs.p6018 := @measurableSet_isLiveState
private theorem measurable_blockBondScores (hS : BondScoreProperties) (hfit : R.params.Admissible) (V : TorusField n)
    (b : BaseChoice R.params.side n) (Y : TorusSite n) : Measurable fun W : TorusField (n * R.params.side) => blockBondScores (R := R) W V b Y := by apply _root_.YangMills.SharedProofs.p16256 <;> assumption
private theorem measurable_liveCase (hS : BondScoreProperties) (hfit : R.params.Admissible) (hrow : R.HasExpansions) (A : ResponseSetup R)
    (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => liveCaseFunction (centeredSupportResponse A V f) p.1 Yt p.2 bad b := by
  classical
  have hl := measurableSet_isLiveState hrow hb Yt
  obtain ⟨v, hv⟩ : ∃ v, v = caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f, A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f := ⟨_, rfl⟩
  have e : (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => liveCaseFunction (centeredSupportResponse A V f) p.1 Yt p.2 bad b) = fun p =>
      ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then A.hull (n * R.params.side) y p.1 Yt p.2 f else 0) +
        (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
          R.params.coupling / 2 * A.coeff * ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
            blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) p.1 V b Y - d - v else 0) := by
    funext p
    have hX : centeredSupportResponse A V f p.1 Yt p.2 bad b = supportResponseSum A V f p.1 Yt p.2 bad b - v := by
      rw [hv]
      rfl
    unfold liveCaseFunction
    rw [hX]
    unfold supportResponseSum centeredHullResponse
    by_cases hp : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
    · simp only [if_pos hp, Finset.sum_sub_distrib, ← hd]
      ring
    · simp [hp]
  rw [e]
  refine (Finset.measurable_sum _ fun y _ => hres.bounds.hull_borel _ hb y Yt f).add
    (Measurable.ite hl (((Measurable.const_mul (Finset.measurable_sum _ fun Y _ =>
      ((measurable_blockBondScores hS hfit V b Y).comp measurable_fst).const_mul _) _).sub_const _).sub_const _) measurable_const)
abbrev _root_.YangMills.SharedProofs.p81506 := @measurable_liveCase
end Borel
section Sizes
variable {A : ResponseSetup R}
private theorem abs_blockBondScores_le (hS : BondScoreProperties) (hfit : R.params.Admissible) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : BaseChoice R.params.side n) (Y : TorusSite n) : |blockBondScores (R := R) W V b Y| ≤ 16 := by apply _root_.YangMills.SharedProofs.p16371 <;> assumption
private theorem exists_lowerSite_of_upperSite (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) {Y : TorusSite n} (hY : Y ∈ upperSites f) :
    ∃ y ∈ lowerSites f, parentBlock R.params.side y = Y := by
  classical
  obtain ⟨p, ⟨hlt, c, hc, hcY⟩, hp⟩ := (Finset.mem_filter.mp hY).2
  obtain ⟨y, hy, hcy⟩ := Finset.mem_biUnion.mp hcY
  have hb : parentBlock R.params.side y = Y := by simpa [sitesInBlocks] using hy
  exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, ⟨hlt, c, hc, hcy⟩, hp⟩, hb⟩
abbrev _root_.YangMills.SharedProofs.p21292 := @exists_lowerSite_of_upperSite
private theorem card_upperSites_le (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    (upperSites (R := R) f).card ≤ (lowerSites f).card := by
  classical
  refine Finset.card_le_card_of_surjOn (parentBlock R.params.side) fun Y hY => ?_
  obtain ⟨y, hy, hb⟩ := exists_lowerSite_of_upperSite f hY
  exact ⟨y, hy, hb⟩
abbrev _root_.YangMills.SharedProofs.p7582 := @card_upperSites_le
private theorem siteScore_nonneg (hs : ∀ w, 0 ≤ A.score w) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (y : TorusSite (n * R.params.side)) : 0 ≤ siteScore A.score Yt ωt y := by
  classical
  unfold siteScore
  split_ifs
  · exact hs _
  · exact le_rfl
abbrev _root_.YangMills.SharedProofs.p46846 := @siteScore_nonneg
private theorem C₀_ge_and_one_le_coupling (hfit : R.params.Admissible) (hres : A.IsAdmissible) : 12 + 40 * R.params.coupling ≤ A.responseParams.C₀ ∧ 1 ≤ R.params.coupling := by
  have h := hres.params_admissible
  have h1 := h.C₀_eq
  have h2 := h.N₀_nonneg
  have h3 := h.Kc_ge
  exact ⟨by linarith, hfit.a_ge⟩
abbrev _root_.YangMills.SharedProofs.p4770 := @C₀_ge_and_one_le_coupling
private theorem abs_supportResponseSum_le (hS : BondScoreProperties) (hW : WeightsCloseToBlockMeans) (hfit : R.params.Admissible)
    (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (h1 : weightNorm R.params.side (R.depth + 1) f ≤ 1) (h0 : weightNorm R.params.side R.depth f ≤ 1) {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω} (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    |supportResponseSum A V f W Yt ωt bad b| ≤
      (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Yt ωt := by
  classical
  obtain ⟨hC, ha⟩ := C₀_ge_and_one_le_coupling hfit hres
  have hs := hres.price.nonneg
  have hodd := hfit.L_odd
  have hF : |∑ y ∈ lowerSites f, centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f| ≤
      A.responseParams.C₀ * ((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Yt ωt := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have each : ∀ y ∈ lowerSites f, |centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f| ≤ A.responseParams.C₀ + siteScore A.score Yt ωt y := by
      intro y _
      have h2 := hres.bounds.size_hull _ hb y W Yt ωt hl f
      have h3 : 0 ≤ A.responseParams.C₀ + siteScore A.score Yt ωt y := by
        have := siteScore_nonneg hs Yt ωt y
        linarith
      exact h2.trans (mul_le_of_le_one_right h3 h0)
    refine (Finset.sum_le_sum each).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rfl
  have hcoef : |R.params.coupling / 2 * A.coeff| ≤ R.params.coupling := by
    have hal := hres.abs_coeff_le
    rw [abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < R.params.coupling)]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    calc R.params.coupling / 2 * |A.coeff| ≤ R.params.coupling / 2 * 2 := mul_le_mul_of_nonneg_left hal (by linarith)
      _ = R.params.coupling := by ring
  have hsum : |∑ Y ∈ upperSites (R := R) f, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V b Y| ≤
      16 * ((lowerSites f).card : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have each : ∀ Y ∈ upperSites (R := R) f, |blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V b Y| ≤ 16 := by
      intro Y _
      have hh : |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1 :=
        ((hW R.params.side hodd (R.depth + 1) n Y).1 f).trans ((le_max_left _ _).trans h1)
      rw [abs_mul]
      calc _ ≤ 1 * 16 := mul_le_mul hh (abs_blockBondScores_le hS hfit W V b Y) (abs_nonneg _) zero_le_one
        _ = 16 := by norm_num
    refine (Finset.sum_le_sum each).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have : ((upperSites (R := R) f).card : ℝ) ≤ ((lowerSites f).card : ℝ) := by exact_mod_cast card_upperSites_le f
    linarith
  have hm : |R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites (R := R) f,
      blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V b Y| ≤ 16 * R.params.coupling * ((lowerSites f).card : ℝ) := by
    rw [abs_mul]
    calc _ ≤ R.params.coupling * (16 * ((lowerSites f).card : ℝ)) :=
          mul_le_mul hcoef hsum (abs_nonneg _) (by linarith)
      _ = _ := by ring
  show |∑ y ∈ lowerSites f, centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f +
    R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites (R := R) f, blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V b Y| ≤ _
  refine (abs_add_le _ _).trans ?_
  linarith
abbrev _root_.YangMills.SharedProofs.p46704 := @abs_supportResponseSum_le
private theorem cutoffFactor_mem_unit {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) (hρ : 0 < ρ) {u : ℝ} (h0 : 0 ≤ u) :
    0 ≤ cutoffFactor ρ p u ∧ cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.cutoffFactor_nonneg_le_one <;> assumption
private theorem isLiveState_of_stepWeight_ne_zero (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params (n * R.params.side)) {C : Finset (TorusSite n)} {V : TorusField n}
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω} {bad : Finset (TorusBond (n * R.params.side))}
    {b : BaseChoice R.params.side n} (hh : IsHullState R.params R.range W Yt) (hw : stepWeight R C V W Yt ωt bad b ≠ 0) :
    IsLiveState R.params R.coupling R.labelWeight W Yt ωt := by
  refine ⟨hh, lt_of_le_of_ne (hrow.2.nonneg _ hb W Yt ωt hh) fun h => hw ?_⟩
  unfold stepWeight
  rw [← h]
  simp
abbrev _root_.YangMills.SharedProofs.p15857 := @isLiveState_of_stepWeight_ne_zero
private theorem stepWeight_nonneg (hrow : R.HasExpansions) (hcut : IsCutoff R.ballRadius R.barrierFn) (hρ : 0 < R.ballRadius) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ωt bad b := by
  classical
  unfold stepWeight
  refine mul_nonneg (mul_nonneg (mul_nonneg (hrow.2.nonneg _ hb W Yt ωt hh) ?_) ?_) ?_
  · unfold baseLaw
    split_ifs <;> positivity
  · refine Finset.prod_nonneg fun c _ => ?_
    unfold bondKernel
    exact div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
  · unfold markProduct
    refine Finset.prod_nonneg fun e _ => ?_
    have : 0 ≤ bondMark R V W e ∧ bondMark R V W e ≤ 1 := cutoffFactor_mem_unit hcut hρ (norm_nonneg _)
    split_ifs
    · linarith [this.2]
    · exact this.1
abbrev _root_.YangMills.SharedProofs.p32517 := @stepWeight_nonneg
private theorem abs_caseMean_le (hrow : R.HasExpansions) (hcut : IsCutoff R.ballRadius R.barrierFn) (hρ : 0 < R.ballRadius) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) {F B : CaseFunction R n} {c : ℝ} (hc : 0 ≤ c)
    (hB : CaseIntegrable R C V q B)
    (hle : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → |F W Yt ωt bad b| ≤ c * B W Yt ωt bad b) :
    |caseMean R C V q F| ≤ c * caseMean R C V q B := by
  classical
  have hterm : ∀ bad Yt b W ν, ‖caseTerm R C V q F bad Yt b W ν‖ ≤ c * caseTerm R C V q B bad Yt b W ν := by
    intro bad Yt b W ν
    unfold caseTerm
    split_ifs with hcs
    · by_cases hw : stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = 0
      · simp [hw]
      · have h1 := hle _ _ _ bad b (isLiveState_of_stepWeight_ne_zero hrow hb hcs.1 hw)
        have h2 := stepWeight_nonneg hrow hcut hρ hb C V (q.fillLabels Yt ν) bad b hcs.1
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right h1 h2
    · simp
  have hI : |caseIntegral R C V q F| ≤ c * caseIntegral R C V q B := by
    unfold caseIntegral
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun bad hbad => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun Yt _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    have hi := hB bad hbad Yt b
    have hin : ∀ᵐ W ∂(fieldHaar (n * R.params.side)), Integrable (fun ν => caseTerm R C V q B bad Yt b W ν)
        (Measure.pi fun _ => R.labels.μ) := hi.prod_right_ae
    have hout : Integrable (fun W => ∫ ν, caseTerm R C V q B bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ))
        (fieldHaar (n * R.params.side)) := hi.integral_prod_left
    have hh : ‖∫ W, ∫ ν, caseTerm R C V q F bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))‖ ≤
        ∫ W, c * ∫ ν, caseTerm R C V q B bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
      refine norm_integral_le_of_norm_le (hout.const_mul c) (hin.mono fun W hW => ?_)
      have h2 : ‖∫ ν, caseTerm R C V q F bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ)‖ ≤
          ∫ ν, c * caseTerm R C V q B bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) :=
        norm_integral_le_of_norm_le (hW.const_mul c) (Filter.Eventually.of_forall fun ν => hterm bad Yt b W ν)
      rwa [integral_const_mul] at h2
    rw [integral_const_mul, Real.norm_eq_abs] at hh
    exact hh
  have hZ : 0 ≤ coarseStateWeight R C V q := ENNReal.toReal_nonneg
  unfold caseMean
  rw [abs_div, abs_of_nonneg hZ, mul_div_assoc']
  exact div_le_div_of_nonneg_right hI hZ
abbrev _root_.YangMills.SharedProofs.p20584 := @abs_caseMean_le
private theorem trivialField_isCold {σ : ℝ} (m : ℕ) (hσ : 0 < σ) : IsCold σ (trivialField m) := by
  intro x μ ν _
  have : curvature (trivialField m) x μ ν = 0 := by
    simp [curvature, holonomy, trivialField]
  rw [this]
  exact hσ
abbrev _root_.YangMills.SharedProofs.p35782 := @trivialField_isCold
end Sizes
end SupportResponseBound
open SupportResponseBound in
theorem supportResponseBound (hM : meanSiteScoresStepBound) (hS : BondScoreProperties)
    (hW : WeightsCloseToBlockMeans) : supportResponseBoundStatement := by
  classical
  obtain ⟨rt₀, hrt₀, hM⟩ := hM
  refine ⟨rt₀, hrt₀, fun T hT hrt K => ?_⟩
  obtain ⟨y₁, hM⟩ := hM T hT hrt K
  have hκ₁ : 0 < T.κ₁ := by
    have h1 := hT.κ_pos
    have h2 := hT.cE_pos
    have h3 := hT.σ_pos
    unfold ParameterAssignment.κ₁
    exact lt_min (by positivity) (by positivity)
  have hch : 0 < T.gasRate := by
    have h1 := hT.κ_pos
    have h2 := hT.cE_pos
    have h3 := hT.σ_pos
    unfold ParameterAssignment.gasRate
    exact mul_pos (by positivity) (lt_min h2 (lt_min (by positivity) (by positivity)))
  refine ⟨max (max y₁ T.floorMin) (1 / T.gasRate), fun y hy R A hK hAt n _ hn V f hs1 hs0 hne => ?_⟩
  have hy1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : 1 / T.gasRate ≤ y := (le_max_right _ _).trans hy
  have hR := hAt.onFamily
  have hfit : R.params.Admissible := hR.params_eq ▸ hT.fits y hy2
  have hrow : R.HasExpansions := hR.isStep.1
  have hres := hAt.admissible
  have hσ : 0 < R.params.threshold := hfit.σ_pos
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    positivity
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [hR.params_eq]
      rfl
    rw [e, hR.barrierFn_eq]
    exact hT.cut
  have hb : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left n rfl, ?_⟩
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ hn
  refine ⟨fun Yt bad b => measurable_liveCase hS hfit hrow A hres hb V f Yt bad b, ?_, ?_⟩
  · intro W Yt ωt bad b u hl hu _
    unfold liveCaseFunction
    rw [if_pos (isLiveState_gauge hfit hrow hb u hl), if_pos hl]
    unfold centeredSupportResponse
    rw [supportResponseSum_gauge A hres hb V f bad hl hu]
  · intro W Yt ωt bad b hl
    obtain ⟨hC, ha⟩ := C₀_ge_and_one_le_coupling hfit hres
    have hs := hres.price.nonneg
    obtain ⟨Y₀, hY₀⟩ := hne
    obtain ⟨y₀', hy₀', -⟩ := exists_lowerSite_of_upperSite f hY₀
    have hcard : (0 : ℝ) < ((lowerSites f).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨y₀', hy₀'⟩
    obtain ⟨hMi, hMm⟩ := hM y hy1 R A hK hAt n (coldCaseGround R (trivialField n))
      (Or.inl ⟨hn, trivialField_isCold n (by positivity), rfl, rfl, rfl⟩) 1 (fun _ => lowerSites f)
      (fun _ => ⟨y₀', hy₀'⟩) (fun i j hij => absurd (Subsingleton.elim i j) hij)
    have hx1 : 1 ≤ T.gasRate * R.coupling := by
      have h1 : 1 / T.gasRate ≤ R.coupling := hy3.trans hR.le_coupling
      rw [div_le_iff₀ hch] at h1
      linarith
    have hexp : Real.exp (((1 : ℕ) : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling))) ≤ 3 / 2 := by
      have hu1 : Real.exp (-(7 * T.gasRate * R.coupling)) ≤ 1 / 8 := by
        have h1 := Real.add_one_le_exp (7 * T.gasRate * R.coupling)
        have h2 : Real.exp (-(7 * T.gasRate * R.coupling)) * Real.exp (7 * T.gasRate * R.coupling) = 1 := by
          rw [← Real.exp_add]
          simp
        have h3 := Real.exp_pos (-(7 * T.gasRate * R.coupling))
        nlinarith
      have hu0 := Real.exp_pos (-(7 * T.gasRate * R.coupling))
      obtain ⟨u, hu⟩ : ∃ u, u = Real.exp (-(7 * T.gasRate * R.coupling)) := ⟨_, rfl⟩
      rw [← hu] at hu1 hu0 ⊢
      rw [Nat.cast_one, one_mul]
      have h1 := Real.add_one_le_exp (-u)
      have h2 : Real.exp u * Real.exp (-u) = 1 := by
        rw [← Real.exp_add]
        simp
      by_contra hcon
      push Not at hcon
      have h3 : (7 : ℝ) / 8 ≤ Real.exp (-u) := by linarith
      nlinarith
    have hparent : (∏ i : Fin 1, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks ((fun _ => lowerSites f) i))
        (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2) = 1 := by
      rw [Fin.prod_univ_one]
      unfold meanSiteScore
      have : ∀ z, siteScore (coarseLabelScore A.responseParams.s₁ A.score) (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2 z = 0 := by
        intro z
        unfold siteScore
        rw [dif_neg]
        exact Finset.notMem_empty _
      simp [this]
    rw [hparent, mul_one] at hMm
    have hEN : caseMean R ∅ (trivialField n) (emptyCoarseState R) (fun _ Yt ωt _ _ => meanSiteScore A.score (lowerSites f) Yt ωt) ≤ 3 / 2 := by
      refine le_trans (le_of_eq ?_) (hMm.trans hexp)
      show _ = caseMean R ∅ (trivialField n) (emptyCoarseState R) (prodMeanSiteScores A fun _ : Fin 1 => lowerSites f)
      congr 1
      funext _ Yt ωt _ _
      simp [prodMeanSiteScores]
    have hIN : CaseIntegrable R ∅ (trivialField n) (emptyCoarseState R) (fun _ Yt ωt _ _ => meanSiteScore A.score (lowerSites f) Yt ωt) := by
      have e : (fun (_ : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
          (_ : Finset (TorusBond (n * R.params.side))) (_ : BaseChoice R.params.side n) => meanSiteScore A.score (lowerSites f) Yt ωt) =
          prodMeanSiteScores A fun _ : Fin 1 => lowerSites f := by
        funext _ Yt ωt _ _
        simp [prodMeanSiteScores]
      rw [e]
      exact hMi
    have hN : ∀ (Y' : Finset (TorusSite (n * R.params.side))) (ω' : Y' → R.labels.Ω),
        ((lowerSites f).card : ℝ) * meanSiteScore A.score (lowerSites f) Y' ω' =
          ((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Y' ω' := by
      intro Y' ω'
      unfold meanSiteScore scoreSumOn
      field_simp
    have hS0 : ∀ (Y' : Finset (TorusSite (n * R.params.side))) (ω' : Y' → R.labels.Ω), 0 ≤ scoreSumOn A (lowerSites f) Y' ω' :=
      fun Y' ω' => Finset.sum_nonneg fun y _ => siteScore_nonneg hs Y' ω' y
    have hc1 : 1 ≤ A.responseParams.C₀ + 16 * R.params.coupling := by linarith
    have hc0 : 0 ≤ (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) := by positivity
    have hv : |caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| ≤
        (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) * (3 / 2) := by
      refine (abs_caseMean_le hrow hcut hρ hb ∅ (trivialField n) (emptyCoarseState R) hc0 hIN fun W' Y' ω' bad' b' hl' => ?_).trans
        (mul_le_mul_of_nonneg_left hEN hc0)
      refine (abs_supportResponseSum_le hS hW hfit hres hb (trivialField n) f hs1 hs0 bad' b' hl').trans ?_
      have h1 := hN Y' ω'
      have h2 := hS0 Y' ω'
      show _ ≤ (A.responseParams.C₀ + 16 * R.params.coupling) * ((lowerSites f).card : ℝ) * meanSiteScore A.score (lowerSites f) Y' ω'
      rw [mul_assoc, h1]
      nlinarith
    have hF := abs_supportResponseSum_le hS hW hfit hres hb V f hs1 hs0 bad b hl
    unfold centeredSupportResponse
    refine (abs_sub _ _).trans ?_
    have h1 := hN Yt ωt
    have h2 := hS0 Yt ωt
    show _ ≤ 4 * (A.responseParams.C₀ * ((lowerSites f).card : ℝ)) * meanSiteScore A.score (lowerSites f) Yt ωt
    have e : 4 * (A.responseParams.C₀ * ((lowerSites f).card : ℝ)) * meanSiteScore A.score (lowerSites f) Yt ωt =
        4 * A.responseParams.C₀ * (((lowerSites f).card : ℝ) + scoreSumOn A (lowerSites f) Yt ωt) := by
      rw [← h1]
      ring
    rw [e]
    nlinarith
end YangMills.Construction.FreeEnergies
end
