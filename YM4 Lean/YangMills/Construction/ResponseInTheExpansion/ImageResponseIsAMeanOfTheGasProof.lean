import YangMills.Construction.ClusterExpansionOfAStep.CaseFunctionIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.ClusterExpansionOfAStep.MeanOfTheGainProof
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportVariablesHaveTheirSizesProof
import YangMills.Construction.ResponseInTheExpansion.CaseMeanIsAMeanOfTheGas
import YangMills.Construction.ResponseInTheExpansion.GasIntegrandIsBorel
import YangMills.Construction.ResponseInTheExpansion.ImageResponseIsAMeanOfTheGas
import YangMills.Construction.ResponseInTheExpansion.ResponseInTwoSettingsProof
import YangMills.Construction.ResponseInTheExpansion.SiteScoreHasAMajorant
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open Dobrushin ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepGas StepCosts RenormalizationStepParameters ClusterExpansionOfAStep
namespace WeightedResponses
namespace GasMeanOfResponse
section Means
variable {n : ℕ} {free : Finset (TorusBond n)}
private theorem abs_weightedMean_le {d G : FreeCoords free → ℝ} {M : ℝ} (hd : ∀ η, 0 ≤ d η) (hM : 0 ≤ M)
    (hG : ∀ η, d η ≠ 0 → |G η| ≤ M) : |weightedMean d G| ≤ M := by
  unfold weightedMean
  by_cases hi : Integrable d
  · have h0 : 0 ≤ ∫ η, d η := integral_nonneg hd
    rcases h0.eq_or_lt with h | h
    · rw [← h, div_zero, abs_zero]
      exact hM
    · rw [abs_div, abs_of_pos h, div_le_iff₀ h]
      calc |∫ η, G η * d η| ≤ ∫ η, |G η * d η| := abs_integral_le_integral_abs
        _ ≤ ∫ η, M * d η := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hi.const_mul M)
              (Filter.Eventually.of_forall fun η => ?_)
            by_cases h0 : d η = 0
            · simp [h0]
            · show |G η * d η| ≤ M * d η
              rw [abs_mul, abs_of_nonneg (hd η)]
              exact mul_le_mul_of_nonneg_right (hG η h0) (hd η)
        _ = M * ∫ η, d η := integral_const_mul _ _
  · rw [integral_undef hi, div_zero, abs_zero]
    exact hM
private theorem weightedMean_congr_of_ne_zero {d G G' : FreeCoords free → ℝ} (h : ∀ η, d η ≠ 0 → G η = G' η) :
    weightedMean d G = weightedMean d G' := by
  unfold weightedMean
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  by_cases h0 : d η = 0
  · simp [h0]
  · show G η * d η = G' η * d η
    rw [h η h0]
abbrev _root_.YangMills.SharedProofs.p17143 := @weightedMean_congr_of_ne_zero
private theorem integrable_mul_density_of_bound {d G : FreeCoords free → ℝ} {M : ℝ} (hi : Integrable d)
    (hd : ∀ η, 0 ≤ d η) (hGm : Measurable G) (hG : ∀ η, d η ≠ 0 → |G η| ≤ M) :
    Integrable fun η => G η * d η := by
  refine Integrable.mono' (hi.const_mul M) (hGm.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun η => ?_)
  by_cases h0 : d η = 0
  · simp [h0]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd η)]
    exact mul_le_mul_of_nonneg_right (hG η h0) (hd η)
abbrev _root_.YangMills.SharedProofs.p24304 := @integrable_mul_density_of_bound
private theorem weightedMean_add {d G G' : FreeCoords free → ℝ} (h1 : Integrable fun η => G η * d η)
    (h2 : Integrable fun η => G' η * d η) :
    weightedMean d (fun η => G η + G' η) = weightedMean d G + weightedMean d G' := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GainMean.weightedMean_add <;> assumption
private theorem weightedMean_sum {ι : Type*} (s : Finset ι) {d : FreeCoords free → ℝ} (f : ι → FreeCoords free → ℝ)
    (h : ∀ i ∈ s, Integrable fun η => f i η * d η) :
    weightedMean d (fun η => ∑ i ∈ s, f i η) = ∑ i ∈ s, weightedMean d (f i) := by
  unfold weightedMean
  rw [← Finset.sum_div, ← integral_finsetSum s h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  show (∑ i ∈ s, f i η) * d η = ∑ i ∈ s, f i η * d η
  rw [Finset.sum_mul]
private theorem weightedMean_const_mul (c : ℝ) (d G : FreeCoords free → ℝ) :
    weightedMean d (fun η => c * G η) = c * weightedMean d G := by
  unfold weightedMean
  rw [mul_div_assoc', ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  show c * G η * d η = c * (G η * d η)
  ring
private theorem weightedMean_sub_const {d G : FreeCoords free → ℝ} (c : ℝ) (hi : Integrable d) (hZ : ∫ η, d η ≠ 0)
    (h1 : Integrable fun η => G η * d η) : weightedMean d (fun η => G η - c) = weightedMean d G - c := by
  unfold weightedMean
  have e : ∫ η, (G η - c) * d η = (∫ η, G η * d η) - c * ∫ η, d η := by
    rw [← integral_const_mul, ← integral_sub h1 (hi.const_mul c)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show (G η - c) * d η = G η * d η - c * d η
    ring
  rw [e]
  field_simp
end Means
section Cutoff
private theorem cutoffFactor_le_one {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hc : IsCutoff ρ p) {t : ℝ} (h0 : 0 ≤ t) :
    cutoffFactor ρ p t ≤ 1 := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_le_one <;> assumption
private theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
end Cutoff
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Gauges
private theorem isHullState_gaugeTransform (hfit : R.params.Admissible)
    (g : TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion) (W : TorusField (n * R.params.side)) (r : ℕ)
    (Y : Finset (TorusSite (n * R.params.side))) :
    IsHullState R.params r (gaugeTransform g W) Y ↔ IsHullState R.params r W Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.isHullState_gaugeTransform_iff <;> assumption
private theorem contourMean_gaugeTransform_of_bases {g : TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion}
    (W : TorusField (n * R.params.side)) {b : BaseChoice R.params.side n}
    (hb : ∀ e, g (toTorusSite (n * R.params.side) (b e)) = 1) (c : (stepBlockFrame R.params.side n).Cell × Fin 4) :
    LumpContours.contourMean R.params.baseDepth (stepHotLumps R.params (gaugeTransform g W)) b
        (readAtLevel (stepBlockFrame R.params.side n) 0 (gaugeTransform g W)) c =
      LumpContours.contourMean R.params.baseDepth (stepHotLumps R.params W) b
        (readAtLevel (stepBlockFrame R.params.side n) 0 W) c := by apply _root_.YangMills.SharedProofs.p5543 <;> assumption
private theorem bondScore_gaugeTransform {g : TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion}
    (W : TorusField (n * R.params.side)) (V : TorusField n) {b : BaseChoice R.params.side n}
    (hb : ∀ e, g (toTorusSite (n * R.params.side) (b e)) = 1) (c : TorusBond n) :
    bondScore R.params R.coupling (gaugeTransform g W) V b c = bondScore R.params R.coupling W V b c := by
  have hfit : ∀ U : TorusField n, bondFit R.params (gaugeTransform g W) U b c = bondFit R.params W U b c := by
    intro U
    unfold bondFit LumpContours.contourFit
    rw [contourMean_gaugeTransform_of_bases (R := R) W hb]
  have hker : ∀ U : TorusField n, bondKernelAt R.params R.coupling (gaugeTransform g W) U b c =
      bondKernelAt R.params R.coupling W U b c := by
    intro U
    have hm := contourMean_gaugeTransform_of_bases (R := R) W hb
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)
    show Real.exp (R.params.coupling * R.coupling * (LumpContours.contourMean R.params.baseDepth
        (stepHotLumps R.params (gaugeTransform g W)) b
        (readAtLevel (stepBlockFrame R.params.side n) 0 (gaugeTransform g W))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2) *
          (((readAtLevel (stepBlockFrame R.params.side n) 1 U) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1)
            c.2)⁻¹ : BlockAverages.UnitQuaternion)).re) /
        partitionFn (R.params.coupling * R.coupling * ‖LumpContours.contourMean R.params.baseDepth
          (stepHotLumps R.params (gaugeTransform g W)) b
          (readAtLevel (stepBlockFrame R.params.side n) 0 (gaugeTransform g W))
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)‖) =
      Real.exp (R.params.coupling * R.coupling * (LumpContours.contourMean R.params.baseDepth
        (stepHotLumps R.params W) b
        (readAtLevel (stepBlockFrame R.params.side n) 0 W) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2) *
          (((readAtLevel (stepBlockFrame R.params.side n) 1 U) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1)
            c.2)⁻¹ : BlockAverages.UnitQuaternion)).re) /
        partitionFn (R.params.coupling * R.coupling * ‖LumpContours.contourMean R.params.baseDepth
          (stepHotLumps R.params W) b
          (readAtLevel (stepBlockFrame R.params.side n) 0 W) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)‖)
    rw [hm]
  unfold bondScore fitConditionalMean
  rw [hfit V]
  simp only [hfit, hker]
abbrev _root_.YangMills.SharedProofs.p31057 := @bondScore_gaugeTransform
end Gauges
section Cases
private structure IsRealCase (H : CaseFunction R n) : Prop where
  borel : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n),
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => H p.1 Yt p.2 bad b
  gauge : IsGaugeInvariantCase H
private def weightOfCase (f : ℝ → ℝ≥0∞) (H : CaseFunction R n) : CaseFunctional R n :=
  fun W Yt ωt bad b => f (H W Yt ωt bad b)
private theorem isCaseFunctional_weightOfCase {H : CaseFunction R n} (hH : IsRealCase H) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) : IsCaseFunctional (weightOfCase f H) :=
  ⟨fun Yt bad b => hf.comp (hH.borel Yt bad b), fun W Yt ωt bad b u hh hp h1 h2 =>
    congrArg f (hH.gauge W Yt ωt bad b u ⟨hh, hp⟩ h1 h2)⟩
private theorem measurable_ofReal_pos : Measurable fun u : ℝ => ENNReal.ofReal u := ENNReal.measurable_ofReal
private theorem measurable_ofReal_neg : Measurable fun u : ℝ => ENNReal.ofReal (-u) :=
  ENNReal.measurable_ofReal.comp measurable_neg
private theorem measurable_ofReal_abs : Measurable fun u : ℝ => ENNReal.ofReal |u| :=
  ENNReal.measurable_ofReal.comp continuous_abs.measurable
end Cases
section Charts
private theorem chartDensity_nonneg (s : ChartSetting R n) (η : FreeCoords s.free) : 0 ≤ chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_nonneg <;> assumption
private theorem inBalls_of_chartDensity_ne_zero (s : ChartSetting R n) {η : FreeCoords s.free}
    (h : chartDensity s η ≠ 0) : s.InBalls η := by apply _root_.YangMills.SharedProofs.p4538 <;> assumption
private theorem isLiveState_of_inBalls (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hn : R.params.n₀ ≤ n)
    {s : ChartSetting R n} (hs : s.IsAdmissible) {η : FreeCoords s.free} (hη : s.InBalls η) :
    IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling := by apply _root_.YangMills.SharedProofs.p48283 <;> assumption
private theorem weightNorm_nonneg (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
private theorem siteScore_nonneg {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {m : ℕ} (Y : Finset (TorusSite m))
    (ω : Y → Ω) (y : TorusSite m) : 0 ≤ siteScore s Y ω y := by apply _root_.YangMills.SharedProofs.p22275 <;> assumption
end Charts
section Gas
private def readInChart (G : GasGround R n) (H : CaseFunction R n) (σ : G.Config)
    (η : FreeCoords (configSetting G σ).free) : ℝ :=
  H ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling (G.badBondsOf σ)
    (configSetting G σ).bases
private def chartMean (G : GasGround R n) (H : CaseFunction R n) (σ : G.Config) : ℝ :=
  weightedMean (chartDensity (configSetting G σ)) (readInChart G H σ)
private theorem gasIntegrand_weightOfCase (G : GasGround R n) (f : ℝ → ℝ≥0∞) (H : CaseFunction R n) {σ : G.Config}
    (ha : G.pairConstraint.IsAdmissible σ) :
    G.gasIntegrand (weightOfCase f H) σ =
      ∫⁻ η, f (readInChart G H σ η) * ENNReal.ofReal (chartDensity (configSetting G σ) η) :=
  if_pos ha
private structure GasHypotheses (G : GasGround R n) (z : G.GasSpin → ℝ) : Prop where
  weight : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z
  prob : IsProbabilityMeasure (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight)
  setting : ∀ σ, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible
  density_int : ∀ σ, G.pairConstraint.IsAdmissible σ → Integrable (chartDensity (configSetting G σ))
  density_pos : ∀ σ, G.pairConstraint.IsAdmissible σ → 0 < ∫ η, chartDensity (configSetting G σ) η
  mass : ∀ σ, G.pairConstraint.IsAdmissible σ →
    settingMass (configSetting G σ) = ENNReal.ofReal (∫ η, chartDensity (configSetting G σ) η)
  borel : ∀ F : CaseFunctional R n, IsCaseFunctional F → Measurable (G.gasIntegrand F)
variable {G : GasGround R n} {z : G.GasSpin → ℝ}
private theorem weight_eq_integral (hf : GasHypotheses G z) {σ : G.Config} (ha : G.pairConstraint.IsAdmissible σ) :
    G.weight σ = ∫ η, chartDensity (configSetting G σ) η := by
  have e : G.weight σ = (settingMass (configSetting G σ)).toReal := if_pos ha
  rw [e, hf.mass σ ha, ENNReal.toReal_ofReal (integral_nonneg (chartDensity_nonneg _))]
private theorem weightDensity_eq_settingMass (hf : GasHypotheses G z) {σ : G.Config}
    (ha : G.pairConstraint.IsAdmissible σ) :
    G.pairConstraint.weightDensity G.weight σ = settingMass (configSetting G σ) := by
  have e : G.pairConstraint.weightDensity G.weight σ = ENNReal.ofReal (G.weight σ) := if_pos ha
  rw [e, weight_eq_integral hf ha, hf.mass σ ha]
private theorem total_weight_ne (hf : GasHypotheses G z) :
    ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) ≠ 0 ∧
      ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) ≠ ⊤ := by
  have h1 : G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight Set.univ = 1 := hf.prob.measure_univ
  simp only [PairConstraint.gibbsLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h1
  constructor
  · intro h0
    rw [h0] at h1
    simp at h1
  · intro h0
    rw [h0] at h1
    simp at h1
private theorem ae_isAdmissible (hf : GasHypotheses G z) : ∀ᵐ σ ∂G.gibbsLaw ∅, G.pairConstraint.IsAdmissible σ := by
  rw [ae_iff]
  have hs : MeasurableSet {σ | ¬ G.pairConstraint.IsAdmissible σ} := hf.weight.measurableSet_admissible.compl
  show G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight _ = 0
  simp only [PairConstraint.gibbsLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
  have : ∫⁻ σ in {σ | ¬ G.pairConstraint.IsAdmissible σ}, G.pairConstraint.weightDensity G.weight σ
      ∂Measure.pi (G.referenceMeasure ∅) = 0 := by
    have hz : ∀ σ ∈ {σ | ¬ G.pairConstraint.IsAdmissible σ},
        G.pairConstraint.weightDensity G.weight σ = (fun _ => (0 : ℝ≥0∞)) σ :=
      fun σ hσ => if_neg hσ
    rw [setLIntegral_congr_fun hs hz]
    simp
  rw [this, mul_zero]
private theorem integral_eq_pos_sub_neg (_hf : GasHypotheses G z) (H : CaseFunction R n) {σ : G.Config}
    (ha : G.pairConstraint.IsAdmissible σ)
    (hI : Integrable fun η => readInChart G H σ η * chartDensity (configSetting G σ) η) :
    ∫ η, readInChart G H σ η * chartDensity (configSetting G σ) η =
      (G.gasIntegrand (weightOfCase (fun u => ENNReal.ofReal u) H) σ).toReal -
        (G.gasIntegrand (weightOfCase (fun u => ENNReal.ofReal (-u)) H) σ).toReal := by
  rw [gasIntegrand_weightOfCase G _ H ha, gasIntegrand_weightOfCase G _ H ha,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
  have e1 : ∀ η, ENNReal.ofReal (readInChart G H σ η * chartDensity (configSetting G σ) η) =
      ENNReal.ofReal (readInChart G H σ η) * ENNReal.ofReal (chartDensity (configSetting G σ) η) := fun η =>
    ENNReal.ofReal_mul' (chartDensity_nonneg _ η)
  have e2 : ∀ η, ENNReal.ofReal (-(readInChart G H σ η * chartDensity (configSetting G σ) η)) =
      ENNReal.ofReal (-readInChart G H σ η) * ENNReal.ofReal (chartDensity (configSetting G σ) η) := fun η => by
    rw [← neg_mul]
    exact ENNReal.ofReal_mul' (chartDensity_nonneg _ η)
  simp only [e1, e2]
private theorem integrable_chartMean (hf : GasHypotheses G z) {H : CaseFunction R n} (hH : IsRealCase H)
    (hb : ∀ σ, G.pairConstraint.IsAdmissible σ →
      Integrable fun η => readInChart G H σ η * chartDensity (configSetting G σ) η)
    {B : G.Config → ℝ≥0∞} (hBm : Measurable B)
    (hB : ∀ σ, G.pairConstraint.IsAdmissible σ → ENNReal.ofReal |chartMean G H σ| ≤ B σ)
    (hfin : ∫⁻ σ, B σ * G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) ≠ ⊤) :
    Integrable (chartMean G H) (G.gibbsLaw ∅) := by
  have hadm := ae_isAdmissible hf
  have hp := hf.borel _ (isCaseFunctional_weightOfCase hH measurable_ofReal_pos)
  have hq := hf.borel _ (isCaseFunctional_weightOfCase hH measurable_ofReal_neg)
  have hfm := (hp.ennreal_toReal.sub hq.ennreal_toReal).div hf.weight.measurable
  have hae : chartMean G H =ᵐ[G.gibbsLaw ∅] fun σ =>
      ((G.gasIntegrand (weightOfCase (fun u => ENNReal.ofReal u) H) σ).toReal -
        (G.gasIntegrand (weightOfCase (fun u => ENNReal.ofReal (-u)) H) σ).toReal) / G.weight σ := by
    filter_upwards [hadm] with σ ha
    show weightedMean _ _ = _
    unfold weightedMean
    rw [integral_eq_pos_sub_neg hf H ha (hb σ ha), weight_eq_integral hf ha]
  refine ⟨hfm.aestronglyMeasurable.congr hae.symm, ?_⟩
  have h1 : ∫⁻ σ, ‖chartMean G H σ‖ₑ ∂G.gibbsLaw ∅ ≤ ∫⁻ σ, B σ ∂G.gibbsLaw ∅ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hadm] with σ ha
    rw [Real.enorm_eq_ofReal_abs]
    exact hB σ ha
  have h2 : ∫⁻ σ, B σ ∂G.gibbsLaw ∅ =
      (∫⁻ σ, G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅))⁻¹ *
        ∫⁻ σ, B σ * G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) := by
    show ∫⁻ σ, B σ ∂G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight = _
    rw [PairConstraint.gibbsLaw, lintegral_smul_measure, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul _ hf.weight.measurable_weightDensity hBm]
    simp only [Pi.mul_apply, mul_comm]
  refine lt_of_le_of_lt h1 ?_
  rw [h2]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr (total_weight_ne hf).1)) hfin.lt_top
end Gas
section Response
variable (A : ResponseSetup R)
open Classical in
private def liveHullResponse (y : TorusSite (n * R.params.side))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) : CaseFunction R n :=
  fun W Yt ωt _ _ => if IsLiveState R.params R.coupling R.labelWeight W Yt ωt then
    A.hull (n * R.params.side) y W Yt ωt h else 0
private def scoreCase (V : TorusField n) (c : TorusBond n) : CaseFunction R n :=
  fun W _ _ _ b => bondScore R.params R.coupling W V b c
private def liveBlockCase (V : TorusField n) (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : CaseFunction R n :=
  fun W Yt ωt bad b => ∑ y ∈ sitesInBlocks R.params.side {Y}, liveHullResponse A y h W Yt ωt bad b +
    R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h *
      ∑ i : Fin 4, (scoreCase (R := R) V (Y, i) W Yt ωt bad b +
        scoreCase (R := R) V (Y - unitStep n i, i) W Yt ωt bad b)
variable {A}
private theorem isRealCase_liveHullResponse (hrow : R.HasExpansions) (hfit : R.params.Admissible)
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold
      A.hull A.siteRemainder A.totalRemainder) (hbs : IsBlockTorusSide R.params (n * R.params.side))
    (y : TorusSite (n * R.params.side)) (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) :
    IsRealCase (liveHullResponse A y h : CaseFunction R n) := by
  classical
  refine ⟨fun Yt bad b => hA.hull_borel (n * R.params.side) hbs y Yt h, ?_⟩
  intro W Yt ωt bad b u hl _ _
  have hh : IsHullState R.params (clusterRange R.coupling) (gaugeTransform u W) Yt :=
    (isHullState_gaugeTransform hfit u W _ Yt).mpr hl.1
  have hl' : IsLiveState R.params R.coupling R.labelWeight (gaugeTransform u W) Yt (R.labels.act Yt u ωt) :=
    ⟨hh, by rw [hrow.2.gauge (n * R.params.side) hbs W Yt ωt u hl.1]; exact hl.2⟩
  unfold liveHullResponse
  rw [if_pos hl', if_pos hl]
  exact hA.hull_gauge (n * R.params.side) hbs y u W Yt ωt hl h
private theorem isRealCase_scoreCase (hsb : BondScoreProperties) (hfit : R.params.Admissible) (V : TorusField n)
    (c : TorusBond n) : IsRealCase (scoreCase V c : CaseFunction R n) := by
  refine ⟨fun Yt bad b => ?_, ?_⟩
  · have h1 := (hsb R.params hfit R.coupling n b c).2.2.2.2
    have h2 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => (p.1, V) :=
      measurable_fst.prodMk measurable_const
    have h3 := h1.comp h2
    exact h3
  · intro W Yt ωt bad b u _ h1 _
    exact bondScore_gaugeTransform W V h1 c
private theorem isRealCase_liveBlockCase {V : TorusField n} {Y : TorusSite n}
    {h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    (hc : ∀ y, IsRealCase (liveHullResponse A y h : CaseFunction R n))
    (hs : ∀ c, IsRealCase (scoreCase V c : CaseFunction R n)) : IsRealCase (liveBlockCase A V Y h) := by
  refine ⟨fun Yt bad b => ?_, ?_⟩
  · have h1 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        ∑ y ∈ sitesInBlocks R.params.side {Y}, (liveHullResponse A y h : CaseFunction R n) p.1 Yt p.2 bad b :=
      Finset.measurable_sum _ fun y _ => (hc y).borel Yt bad b
    have h2 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => ∑ i : Fin 4,
        (scoreCase (R := R) V (Y, i) p.1 Yt p.2 bad b + scoreCase (R := R) V (Y - unitStep n i, i) p.1 Yt p.2 bad b) :=
      Finset.measurable_sum _ fun i _ => ((hs _).borel Yt bad b).add ((hs _).borel Yt bad b)
    have h3 := h1.add (h2.const_mul (R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h))
    unfold liveBlockCase
    exact h3
  · intro W Yt ωt bad b u hl h1 h2
    have e1 : ∑ y ∈ sitesInBlocks R.params.side {Y},
          (liveHullResponse A y h : CaseFunction R n) (gaugeTransform u W) Yt (R.labels.act Yt u ωt) bad b =
        ∑ y ∈ sitesInBlocks R.params.side {Y}, (liveHullResponse A y h : CaseFunction R n) W Yt ωt bad b :=
      Finset.sum_congr rfl fun y _ => (hc y).gauge W Yt ωt bad b u hl h1 h2
    have e2 : ∑ i : Fin 4, (scoreCase (R := R) V (Y, i) (gaugeTransform u W) Yt (R.labels.act Yt u ωt) bad b +
          scoreCase (R := R) V (Y - unitStep n i, i) (gaugeTransform u W) Yt (R.labels.act Yt u ωt) bad b) =
        ∑ i : Fin 4, (scoreCase (R := R) V (Y, i) W Yt ωt bad b +
          scoreCase (R := R) V (Y - unitStep n i, i) W Yt ωt bad b) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(hs (Y, i)).gauge W Yt ωt bad b u hl h1 h2, (hs (Y - unitStep n i, i)).gauge W Yt ωt bad b u hl h1 h2]
    unfold liveBlockCase
    rw [e1, e2]
private theorem abs_liveHullResponse_le
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold
      A.hull A.siteRemainder A.totalRemainder)
    (hbs : IsBlockTorusSide R.params (n * R.params.side)) (hC : 0 ≤ A.responseParams.C₀) (hsn : ∀ w, 0 ≤ A.score w)
    (y : TorusSite (n * R.params.side)) (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    |(liveHullResponse A y h : CaseFunction R n) W Yt ωt bad b| ≤
      |A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h| +
        (A.responseParams.C₀ + siteScore A.score Yt ωt y) * weightNorm R.params.side R.depth h := by
  classical
  have hnn : 0 ≤ (A.responseParams.C₀ + siteScore A.score Yt ωt y) * weightNorm R.params.side R.depth h :=
    mul_nonneg (add_nonneg hC (siteScore_nonneg hsn _ _ _)) (weightNorm_nonneg _ _ _)
  unfold liveHullResponse
  split_ifs with hl
  · have h1 := hA.size_hull (n * R.params.side) hbs y W Yt ωt hl h
    unfold centeredHullResponse at h1
    have h2 : |A.hull (n * R.params.side) y W Yt ωt h| ≤
        |A.hull (n * R.params.side) y W Yt ωt h - A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h| +
          |A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h| := by
      have := abs_add_le (A.hull (n * R.params.side) y W Yt ωt h -
          A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h)
        (A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h)
      simpa using this
    linarith
  · rw [abs_zero]
    exact add_nonneg (abs_nonneg _) hnn
private theorem abs_sum_scoreCase_le (hsb : BondScoreProperties) (hfit : R.params.Admissible) (V : TorusField n)
    (Y : TorusSite n) (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    |∑ i : Fin 4, (scoreCase (R := R) V (Y, i) W Yt ωt bad b +
      scoreCase (R := R) V (Y - unitStep n i, i) W Yt ωt bad b)| ≤ 16 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ i : Fin 4, |scoreCase (R := R) V (Y, i) W Yt ωt bad b +
      scoreCase (R := R) V (Y - unitStep n i, i) W Yt ωt bad b| ≤ 4 := by
    intro i
    have e1 : |scoreCase (R := R) V (Y, i) W Yt ωt bad b| ≤ 2 := (hsb R.params hfit R.coupling n b _).2.2.1 W V
    have e2 : |scoreCase (R := R) V (Y - unitStep n i, i) W Yt ωt bad b| ≤ 2 :=
      (hsb R.params hfit R.coupling n b _).2.2.1 W V
    have e3 := abs_add_le (scoreCase (R := R) V (Y, i) W Yt ωt bad b)
      (scoreCase (R := R) V (Y - unitStep n i, i) W Yt ωt bad b)
    linarith
  calc ∑ i : Fin 4, |scoreCase (R := R) V (Y, i) W Yt ωt bad b +
        scoreCase (R := R) V (Y - unitStep n i, i) W Yt ωt bad b|
      ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
    _ = 16 := by norm_num
private theorem stepWeight_nonneg (hrow : R.HasExpansions) (hρ : 0 < R.ballRadius) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hK : BondKernelProperties) (hbs : IsBlockTorusSide R.params (n * R.params.side)) (C : Finset (TorusSite n))
    (V : TorusField n) {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))}
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hh : IsHullState R.params R.range W Yt) : 0 ≤ stepWeight R C V W Yt ωt bad b := by
  classical
  unfold stepWeight
  refine mul_nonneg (mul_nonneg (mul_nonneg (hrow.2.nonneg _ hbs W Yt ωt hh) ?_) ?_) ?_
  · unfold baseLaw
    split_ifs
    · positivity
    · exact le_rfl
  · exact Finset.prod_nonneg fun c _ => (hK.2 _ _ _ _ _ _ _).1.le
  · unfold markProduct
    refine Finset.prod_nonneg fun β _ => ?_
    split_ifs
    · have := cutoffFactor_le_one hρ hcut (t := ‖((chartCoord R.params V W β : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V β : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖)
        (norm_nonneg _)
      unfold bondMark
      linarith
    · exact cutoffFactor_nonneg _ _ _
private theorem caseTerm_caseResponse_eq (hrow : R.HasExpansions) (hbs : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V' V : TorusField n) (q : CoarseState R n) (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
    (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V' q (caseResponse A V Y h) bad Yt b W ν = caseTerm R C V' q (liveBlockCase A V Y h) bad Yt b W ν := by
  classical
  unfold caseTerm
  split_ifs with hc
  · by_cases hl : IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν)
    · congr 1
      unfold caseResponse liveBlockCase liveHullResponse scoreCase blockBondScores
      simp only [if_pos hl]
    · have hz : R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) = 0 :=
        le_antisymm (not_lt.mp fun hp => hl ⟨hc.1, hp⟩) (hrow.2.nonneg _ hbs _ _ _ hc.1)
      have hw : stepWeight R C V' (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = 0 := by
        unfold stepWeight
        rw [hz]
        ring
      rw [hw, mul_zero, mul_zero]
  · rfl
private theorem caseMean_caseResponse_eq (hrow : R.HasExpansions) (hbs : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V' V : TorusField n) (q : CoarseState R n) (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    caseMean R C V' q (caseResponse A V Y h) = caseMean R C V' q (liveBlockCase A V Y h) := by
  unfold caseMean caseIntegral
  simp only [caseTerm_caseResponse_eq hrow hbs]
end Response
section Terms
variable {G : GasGround R n}
private theorem caseTerm_eq_pos_sub_neg {H : CaseFunction R n} (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
    (ν : G.state.unlabelled Yt → R.labels.Ω)
    (hs : ∀ W' ωt, IsHullState R.params R.range W' Yt → 0 ≤ stepWeight R G.cut G.coarse W' Yt ωt bad b) :
    caseTerm R G.cut G.coarse G.state H bad Yt b W ν =
      (G.caseIntegrand (weightOfCase (fun u => ENNReal.ofReal u) H) bad Yt b W ν).toReal -
        (G.caseIntegrand (weightOfCase (fun u => ENNReal.ofReal (-u)) H) bad Yt b W ν).toReal := by
  classical
  unfold caseTerm GasGround.caseIntegrand weightOfCase
  split_ifs with hc
  · have h0 := hs _ (G.state.fillLabels Yt ν) hc.1
    rw [← ENNReal.ofReal_mul' h0, ← ENNReal.ofReal_mul' h0, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', neg_mul]
    exact (max_zero_sub_max_neg_zero_eq_self _).symm
  · simp
private theorem enorm_caseTerm {H : CaseFunction R n} (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
    (ν : G.state.unlabelled Yt → R.labels.Ω)
    (hs : ∀ W' ωt, IsHullState R.params R.range W' Yt → 0 ≤ stepWeight R G.cut G.coarse W' Yt ωt bad b) :
    ‖caseTerm R G.cut G.coarse G.state H bad Yt b W ν‖ₑ =
      G.caseIntegrand (weightOfCase (fun u => ENNReal.ofReal |u|) H) bad Yt b W ν := by
  classical
  unfold caseTerm GasGround.caseIntegrand weightOfCase
  split_ifs with hc
  · have h0 := hs _ (G.state.fillLabels Yt ν) hc.1
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg h0, ENNReal.ofReal_mul' h0]
  · simp
abbrev _root_.YangMills.DeltaSharedProofs.p502092 := @enorm_caseTerm
private theorem integrable_caseTerm {H : CaseFunction R n} (hH : IsRealCase H)
    (hBo : ∀ F : CaseFunctional R n, IsCaseFunctional F → ∀ (bad : Finset (TorusBond (n * R.params.side)))
      (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        G.caseIntegrand F bad Yt b p.1 p.2)
    (hfin : G.caseMass ∅ (weightOfCase (fun u => ENNReal.ofReal |u|) H) ≠ ⊤)
    {bad : Finset (TorusBond (n * R.params.side))} (hbad : bad ∈ (markedBonds R G.cut).powerset)
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hs : ∀ W' ωt, IsHullState R.params R.range W' Yt → 0 ≤ stepWeight R G.cut G.coarse W' Yt ωt bad b) :
    Integrable (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2)
      ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := by
  classical
  have hm : Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
      caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2 := by
    have h1 := (hBo _ (isCaseFunctional_weightOfCase hH measurable_ofReal_pos) bad Yt b).ennreal_toReal
    have h2 := (hBo _ (isCaseFunctional_weightOfCase hH measurable_ofReal_neg) bad Yt b).ennreal_toReal
    have e : (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2) =
        fun p => (G.caseIntegrand (weightOfCase (fun u => ENNReal.ofReal u) H) bad Yt b p.1 p.2).toReal -
          (G.caseIntegrand (weightOfCase (fun u => ENNReal.ofReal (-u)) H) bad Yt b p.1 p.2).toReal :=
      funext fun p => caseTerm_eq_pos_sub_neg bad Yt b p.1 p.2 hs
    rw [e]
    exact h1.sub h2
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  show ∫⁻ p, ‖caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2‖ₑ
    ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) < ⊤
  have e : (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
      ‖caseTerm R G.cut G.coarse G.state H bad Yt b p.1 p.2‖ₑ) =
      fun p => G.caseIntegrand (weightOfCase (fun u => ENNReal.ofReal |u|) H) bad Yt b p.1 p.2 :=
    funext fun p => enorm_caseTerm bad Yt b p.1 p.2 hs
  rw [e, lintegral_prod _ (hBo _ (isCaseFunctional_weightOfCase hH measurable_ofReal_abs) bad Yt b).aemeasurable]
  refine lt_of_le_of_lt ?_ hfin.lt_top
  have hoff : G.CaseAvoids ∅ bad Yt := ⟨fun _ _ _ => by simp, fun _ _ _ => by simp⟩
  set Fa := weightOfCase (fun u => ENNReal.ofReal |u|) H with hFa
  calc ∫⁻ W, ∫⁻ ν : G.state.unlabelled Yt → R.labels.Ω, G.caseIntegrand Fa bad Yt b W ν
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
      = G.caseIntegral Fa bad Yt b := rfl
    _ ≤ ∑ b' : BaseChoice R.params.side n, G.caseIntegral Fa bad Yt b' :=
        Finset.single_le_sum (f := fun b' => G.caseIntegral Fa bad Yt b') (fun _ _ => zero_le) (Finset.mem_univ b)
    _ = if G.CaseAvoids ∅ bad Yt then ∑ b' : BaseChoice R.params.side n, G.caseIntegral Fa bad Yt b' else 0 :=
        (if_pos hoff).symm
    _ ≤ ∑ Yt' : Finset (TorusSite (n * R.params.side)), if G.CaseAvoids ∅ bad Yt' then
          ∑ b' : BaseChoice R.params.side n, G.caseIntegral Fa bad Yt' b' else 0 :=
        Finset.single_le_sum (f := fun Yt' => if G.CaseAvoids ∅ bad Yt' then
          ∑ b' : BaseChoice R.params.side n, G.caseIntegral Fa bad Yt' b' else 0) (fun _ _ => zero_le)
          (Finset.mem_univ Yt)
    _ ≤ G.caseMass ∅ Fa := by
        unfold GasGround.caseMass
        exact Finset.single_le_sum (f := fun bad' => ∑ Yt' : Finset (TorusSite (n * R.params.side)),
          if G.CaseAvoids ∅ bad' Yt' then ∑ b' : BaseChoice R.params.side n, G.caseIntegral Fa bad' Yt' b' else 0)
          (fun _ _ => zero_le) hbad
end Terms
section Core
private theorem ofReal_affine_le {p s sz C : ℝ} {b : ℝ≥0∞} (hsz : 0 ≤ sz) (hb : ENNReal.ofReal s ≤ b) :
    ENNReal.ofReal (p + (C + s) * sz) ≤ ENNReal.ofReal (p + C * sz) + ENNReal.ofReal sz * b := by
  have e : p + (C + s) * sz = (p + C * sz) + s * sz := by ring
  rw [e]
  refine ENNReal.ofReal_add_le.trans ?_
  gcongr
  rw [mul_comm, ENNReal.ofReal_mul hsz]
  gcongr
private theorem lintegral_affine_mul_ne_top {X : Type*} [MeasurableSpace X] {μ : Measure X} {d B : X → ℝ≥0∞}
    (hd : Measurable d) (hB : Measurable B) (hZ : ∫⁻ σ, d σ ∂μ ≠ ⊤) (hfin : ∫⁻ σ, B σ * d σ ∂μ ≠ ⊤) {k c : ℝ≥0∞}
    (hk : k ≠ ⊤) (hc : c ≠ ⊤) : ∫⁻ σ, (k + c * B σ) * d σ ∂μ ≠ ⊤ := by
  have e : ∀ σ, (k + c * B σ) * d σ = k * d σ + c * (B σ * d σ) := fun σ => by
    rw [add_mul, mul_assoc]
  simp only [e]
  rw [lintegral_add_left (hd.const_mul k), lintegral_const_mul k hd,
    lintegral_const_mul c (show Measurable fun σ => B σ * d σ from hB.mul hd)]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hk hZ, ENNReal.mul_ne_top hc hfin⟩
variable {A : ResponseSetup R} {G : GasGround R n} {z : G.GasSpin → ℝ}
private theorem caseResponse_integrable_and_mean (hrow : R.HasExpansions) (hfit : R.params.Admissible)
    (hn : R.params.n₀ ≤ n) (hρ : 0 < R.ballRadius) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold
      A.hull A.siteRemainder A.totalRemainder)
    (hC₀ : 0 ≤ A.responseParams.C₀) (hsn : ∀ w, 0 ≤ A.score w) (hK : BondKernelProperties)
    (hsb : BondScoreProperties) (hf : GasHypotheses G z)
    (hmaj : ∀ y : TorusSite (n * R.params.side), ∃ B : G.Config → ℝ≥0∞, Measurable B ∧
      (∀ σ, G.pairConstraint.IsAdmissible σ → ENNReal.ofReal (chartSiteScore A (configSetting G σ) y) ≤ B σ) ∧
      ∫⁻ σ, B σ * G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) ≠ ⊤)
    (hBo : ∀ F : CaseFunctional R n, IsCaseFunctional F → ∀ (bad : Finset (TorusBond (n * R.params.side)))
      (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        G.caseIntegrand F bad Yt b p.1 p.2)
    (hsum : ∀ F : CaseFunctional R n, IsCaseFunctional F → G.caseMass ∅ F =
      ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
        ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
          G.gasMass ∅ F)
    (hmean : ∀ F : CaseFunction R n,
      (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
        (b : BaseChoice R.params.side n),
        Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) →
      IsGaugeInvariantCase F → CaseIntegrable R G.cut G.coarse G.state F →
        caseMean R G.cut G.coarse G.state F = gasExpectationOfCase G F)
    (Y : TorusSite n) (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    CaseIntegrable R G.cut G.coarse G.state (caseResponse A G.coarse Y h) ∧
    caseMean R G.cut G.coarse G.state (caseResponse A G.coarse Y h) =
      gasBlockMean A G Y h + ∑ y ∈ sitesInBlocks R.params.side {Y},
        A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h := by
  classical
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hcr : ∀ y, IsRealCase (liveHullResponse A y h : CaseFunction R n) := fun y =>
    isRealCase_liveHullResponse hrow hfit hA hbs y h
  have hsc : ∀ c, IsRealCase (scoreCase G.coarse c : CaseFunction R n) := fun c =>
    isRealCase_scoreCase hsb hfit G.coarse c
  have hF : IsRealCase (liveBlockCase A G.coarse Y h) := isRealCase_liveBlockCase hcr hsc
  choose B hBm hBb hBf using hmaj
  have hd := hf.weight.measurable_weightDensity
  obtain ⟨hZ0, hZt⟩ := total_weight_ne hf
  set sz : ℝ := weightNorm R.params.side R.depth
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) with hsz
  have hsz0 : 0 ≤ sz := weightNorm_nonneg _ _ _
  set cc : ℝ := R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h with hcc
  set Pf : TorusSite (n * R.params.side) → ℝ := fun y =>
    A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h with hPf
  set Bc : TorusSite (n * R.params.side) → G.Config → ℝ≥0∞ := fun y σ =>
    ENNReal.ofReal (|Pf y| + A.responseParams.C₀ * sz) + ENNReal.ofReal sz * B y σ with hBc
  have hBcm : ∀ y, Measurable (Bc y) := fun y => ((hBm y).const_mul _).const_add _
  have hBcf : ∀ y, ∫⁻ σ, Bc y σ * G.pairConstraint.weightDensity G.weight σ
      ∂Measure.pi (G.referenceMeasure ∅) ≠ ⊤ := fun y =>
    lintegral_affine_mul_ne_top hd (hBm y) hZt (hBf y) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hcutB : ∀ (y : TorusSite (n * R.params.side)) (σ : G.Config) η, G.pairConstraint.IsAdmissible σ →
      |readInChart G (liveHullResponse A y h) σ η| ≤
        |Pf y| + (A.responseParams.C₀ + chartSiteScore A (configSetting G σ) y) * sz :=
    fun y σ η _ => abs_liveHullResponse_le hA hbs hC₀ hsn y h _ _ _ _ _
  have hcutE : ∀ (y : TorusSite (n * R.params.side)) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ENNReal.ofReal (|Pf y| + (A.responseParams.C₀ + chartSiteScore A (configSetting G σ) y) * sz) ≤ Bc y σ :=
    fun y σ ha => ofReal_affine_le hsz0 (hBb y σ ha)
  have hmeasS : ∀ {H : CaseFunction R n}, IsRealCase H → ∀ σ, Measurable (readInChart G H σ) := fun hH σ =>
    (hH.borel _ _ _).comp ((ClusterExpansionOfAStep.ChartSetting.measurable_field _).prodMk measurable_const)
  have hintC : ∀ y σ, G.pairConstraint.IsAdmissible σ →
      Integrable fun η => readInChart G (liveHullResponse A y h) σ η * chartDensity (configSetting G σ) η :=
    fun y σ ha =>
      integrable_mul_density_of_bound (hf.density_int σ ha) (chartDensity_nonneg _) (hmeasS (hcr y) σ)
        fun η _ => hcutB y σ η ha
  have hscB : ∀ (c : TorusBond n) (σ : G.Config) η, |readInChart G (scoreCase G.coarse c) σ η| ≤ 2 :=
    fun c σ η => (hsb R.params hfit R.coupling n _ c).2.2.1 _ _
  have hintS : ∀ c σ, G.pairConstraint.IsAdmissible σ →
      Integrable fun η => readInChart G (scoreCase G.coarse c) σ η * chartDensity (configSetting G σ) η :=
    fun c σ ha =>
      integrable_mul_density_of_bound (hf.density_int σ ha) (chartDensity_nonneg _) (hmeasS (hsc c) σ)
        fun η _ => hscB c σ η
  have hIr : ∀ y, Integrable (chartMean G (liveHullResponse A y h)) (G.gibbsLaw ∅) := by
    intro y
    refine integrable_chartMean hf (hcr y) (hintC y) (hBcm y) (fun σ ha => ?_) (hBcf y)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hcutE y σ ha)
    refine abs_weightedMean_le (chartDensity_nonneg _) ?_ fun η _ => hcutB y σ η ha
    exact (abs_nonneg _).trans (hcutB y σ (0 : FreeCoords (configSetting G σ).free) ha)
  have hIs : ∀ c, Integrable (chartMean G (scoreCase G.coarse c)) (G.gibbsLaw ∅) := by
    intro c
    have hfin2 : ∫⁻ σ, (fun _ : G.Config => ENNReal.ofReal 2) σ * G.pairConstraint.weightDensity G.weight σ
        ∂Measure.pi (G.referenceMeasure ∅) ≠ ⊤ := by
      rw [lintegral_const_mul _ hd]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZt
    refine integrable_chartMean hf (hsc c) (hintS c) measurable_const (fun σ _ => ?_) hfin2
    exact ENNReal.ofReal_le_ofReal
      (abs_weightedMean_le (chartDensity_nonneg _) (by norm_num) fun η _ => hscB c σ η)
  set Bt : G.Config → ℝ≥0∞ := fun σ =>
    ∑ y ∈ sitesInBlocks R.params.side {Y}, Bc y σ + ENNReal.ofReal (|cc| * 16) with hBt
  have hBtf : ∫⁻ σ, Bt σ * G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) ≠ ⊤ := by
    have e : ∀ σ, Bt σ * G.pairConstraint.weightDensity G.weight σ =
        ∑ y ∈ sitesInBlocks R.params.side {Y}, Bc y σ * G.pairConstraint.weightDensity G.weight σ +
          ENNReal.ofReal (|cc| * 16) * G.pairConstraint.weightDensity G.weight σ := fun σ => by
      rw [hBt]
      simp only [add_mul, Finset.sum_mul]
    simp only [e]
    rw [lintegral_add_right _ (hd.const_mul _), lintegral_const_mul _ hd,
      lintegral_finsetSum _ (f := fun y σ => Bc y σ * G.pairConstraint.weightDensity G.weight σ)
        fun y _ => (hBcm y).mul hd]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun y _ => hBcf y,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZt⟩
  have hcaseB : ∀ (σ : G.Config) η, G.pairConstraint.IsAdmissible σ →
      ENNReal.ofReal |readInChart G (liveBlockCase A G.coarse Y h) σ η| ≤ Bt σ := by
    intro σ η ha
    have h1 : |readInChart G (liveBlockCase A G.coarse Y h) σ η| ≤
        ∑ y ∈ sitesInBlocks R.params.side {Y},
          (|Pf y| + (A.responseParams.C₀ + chartSiteScore A (configSetting G σ) y) * sz) + |cc| * 16 := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => hcutB y σ η ha)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_sum_scoreCase_le hsb hfit G.coarse Y _ _ _ _ _) (abs_nonneg _)
    have hnn : ∀ y ∈ sitesInBlocks R.params.side {Y},
        0 ≤ |Pf y| + (A.responseParams.C₀ + chartSiteScore A (configSetting G σ) y) * sz :=
      fun y _ => (abs_nonneg _).trans (hcutB y σ (0 : FreeCoords (configSetting G σ).free) ha)
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [ENNReal.ofReal_add (Finset.sum_nonneg hnn) (by positivity), ENNReal.ofReal_sum_of_nonneg hnn]
    exact add_le_add (Finset.sum_le_sum fun y _ => hcutE y σ ha) le_rfl
  have hgas : G.gasMass ∅ (weightOfCase (fun u => ENNReal.ofReal |u|) (liveBlockCase A G.coarse Y h)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hBtf ?_
    refine lintegral_mono fun σ => ?_
    by_cases ha : G.pairConstraint.IsAdmissible σ
    · rw [gasIntegrand_weightOfCase G _ _ ha, weightDensity_eq_settingMass hf ha]
      have hae : AEMeasurable fun η => ENNReal.ofReal (chartDensity (configSetting G σ) η) :=
        (hf.density_int σ ha).aemeasurable.ennreal_ofReal
      calc ∫⁻ η, ENNReal.ofReal |readInChart G (liveBlockCase A G.coarse Y h) σ η| *
              ENNReal.ofReal (chartDensity (configSetting G σ) η)
          ≤ ∫⁻ η, Bt σ * ENNReal.ofReal (chartDensity (configSetting G σ) η) :=
            lintegral_mono fun η => by gcongr; exact hcaseB σ η ha
        _ = Bt σ * settingMass (configSetting G σ) := lintegral_const_mul'' _ hae
    · have e : G.gasIntegrand (weightOfCase (fun u => ENNReal.ofReal |u|) (liveBlockCase A G.coarse Y h)) σ = 0 :=
        if_neg ha
      rw [e]
      exact zero_le
  have hmass : G.caseMass ∅ (weightOfCase (fun u => ENNReal.ofReal |u|) (liveBlockCase A G.coarse Y h)) ≠ ⊤ := by
    rw [hsum _ (isCaseFunctional_weightOfCase hF measurable_ofReal_abs)]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hgas
  have hstep : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) W' ωt,
      IsHullState R.params R.range W' Yt → 0 ≤ stepWeight R G.cut G.coarse W' Yt ωt bad b :=
    fun bad Yt b W' ωt hh => stepWeight_nonneg hrow hρ hcut hK hbs G.cut G.coarse ωt bad b hh
  have hIF : CaseIntegrable R G.cut G.coarse G.state (liveBlockCase A G.coarse Y h) := fun bad hbad Yt b =>
    integrable_caseTerm hF hBo hmass hbad Yt b (hstep bad Yt b)
  refine ⟨?_, ?_⟩
  · intro bad hbad Yt b
    have e : (fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        caseTerm R G.cut G.coarse G.state (caseResponse A G.coarse Y h) bad Yt b p.1 p.2) =
        fun p => caseTerm R G.cut G.coarse G.state (liveBlockCase A G.coarse Y h) bad Yt b p.1 p.2 :=
      funext fun p => caseTerm_caseResponse_eq hrow hbs _ _ _ _ _ _ _ _ _ _ _
    rw [e]
    exact hIF bad hbad Yt b
  rw [caseMean_caseResponse_eq hrow hbs, hmean _ hF.borel hF.gauge hIF]
  have hprob : IsProbabilityMeasure (G.gibbsLaw ∅) := hf.prob
  have hsplit : chartMean G (liveBlockCase A G.coarse Y h) =ᵐ[G.gibbsLaw ∅] fun σ =>
      ∑ y ∈ sitesInBlocks R.params.side {Y}, chartMean G (liveHullResponse A y h) σ +
        cc * ∑ i : Fin 4, (chartMean G (scoreCase G.coarse (Y, i)) σ +
          chartMean G (scoreCase G.coarse (Y - unitStep n i, i)) σ) := by
    filter_upwards [ae_isAdmissible hf] with σ ha
    have hsumI : Integrable fun η =>
        (∑ y ∈ sitesInBlocks R.params.side {Y}, readInChart G (liveHullResponse A y h) σ η) *
          chartDensity (configSetting G σ) η := by
      simp only [Finset.sum_mul]
      exact integrable_finsetSum _ fun y _ => hintC y σ ha
    have hpairI : ∀ i : Fin 4, Integrable fun η =>
        (readInChart G (scoreCase G.coarse (Y, i)) σ η +
          readInChart G (scoreCase G.coarse (Y - unitStep n i, i)) σ η) *
          chartDensity (configSetting G σ) η := fun i => by
      simp only [add_mul]
      exact (hintS _ σ ha).add (hintS _ σ ha)
    have hscI : Integrable fun η => (cc * ∑ i : Fin 4,
        (readInChart G (scoreCase G.coarse (Y, i)) σ η +
          readInChart G (scoreCase G.coarse (Y - unitStep n i, i)) σ η)) *
          chartDensity (configSetting G σ) η := by
      simp only [mul_assoc, Finset.sum_mul]
      exact (integrable_finsetSum _ fun i _ => hpairI i).const_mul cc
    show weightedMean _ (fun η => ∑ y ∈ sitesInBlocks R.params.side {Y}, readInChart G (liveHullResponse A y h) σ η +
        cc * ∑ i : Fin 4, (readInChart G (scoreCase G.coarse (Y, i)) σ η +
          readInChart G (scoreCase G.coarse (Y - unitStep n i, i)) σ η)) = _
    rw [weightedMean_add hsumI hscI, weightedMean_sum _ _ fun y _ => hintC y σ ha, weightedMean_const_mul,
      weightedMean_sum _ _ fun i _ => hpairI i]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    exact weightedMean_add (hintS _ σ ha) (hintS _ σ ha)
  have hresp : ∀ y, G.expectation ∅ (fun σ => chartResponse A (configSetting G σ) y h) =
      G.expectation ∅ (chartMean G (liveHullResponse A y h)) - Pf y := by
    intro y
    have hae : (fun σ => chartResponse A (configSetting G σ) y h) =ᵐ[G.gibbsLaw ∅] fun σ =>
        chartMean G (liveHullResponse A y h) σ - Pf y := by
      filter_upwards [ae_isAdmissible hf] with σ ha
      have h1 : chartResponse A (configSetting G σ) y h = weightedMean (chartDensity (configSetting G σ))
          (fun η => readInChart G (liveHullResponse A y h) σ η - Pf y) := by
        refine weightedMean_congr_of_ne_zero fun η hη => ?_
        have hl := isLiveState_of_inBalls hrow hfit hn (hf.setting σ ha) (inBalls_of_chartDensity_ne_zero _ hη)
        show centeredHullResponse A.cold A.hull (n * R.params.side) y _ _ _ h = (if _ then _ else _) - Pf y
        rw [if_pos hl]
        rfl
      rw [h1, weightedMean_sub_const _ (hf.density_int σ ha) (hf.density_pos σ ha).ne' (hintC y σ ha)]
      rfl
    unfold GasGround.expectation
    rw [integral_congr_ae hae, integral_sub (hIr y) (integrable_const _), integral_const]
    simp
  unfold gasExpectationOfCase gasBlockMean
  have hgm : G.expectation ∅ (fun σ => weightedMean (chartDensity (configSetting G σ)) fun η =>
      liveBlockCase A G.coarse Y h ((configSetting G σ).field η) (configSetting G σ).support
        (configSetting G σ).labelling (G.badBondsOf σ) (configSetting G σ).bases) =
      ∑ y ∈ sitesInBlocks R.params.side {Y}, G.expectation ∅ (chartMean G (liveHullResponse A y h)) +
        cc * ∑ i : Fin 4, (G.expectation ∅ (chartMean G (scoreCase G.coarse (Y, i))) +
          G.expectation ∅ (chartMean G (scoreCase G.coarse (Y - unitStep n i, i)))) := by
    have hP : ∀ i : Fin 4, Integrable (fun σ => chartMean G (scoreCase G.coarse (Y, i)) σ +
        chartMean G (scoreCase G.coarse (Y - unitStep n i, i)) σ) (G.gibbsLaw ∅) := fun i =>
      (hIs _).add (hIs _)
    have hI1 : Integrable (fun σ => ∑ y ∈ sitesInBlocks R.params.side {Y},
        chartMean G (liveHullResponse A y h) σ) (G.gibbsLaw ∅) :=
      integrable_finsetSum _ fun y _ => hIr y
    have hI2 : Integrable (fun σ => cc * ∑ i : Fin 4, (chartMean G (scoreCase G.coarse (Y, i)) σ +
        chartMean G (scoreCase G.coarse (Y - unitStep n i, i)) σ)) (G.gibbsLaw ∅) :=
      (integrable_finsetSum _ fun i _ => hP i).const_mul cc
    unfold GasGround.expectation
    show ∫ σ, chartMean G (liveBlockCase A G.coarse Y h) σ ∂G.gibbsLaw ∅ = _
    rw [integral_congr_ae hsplit, integral_add hI1 hI2, integral_finsetSum _ fun y _ => hIr y, integral_const_mul,
      integral_finsetSum _ fun i _ => hP i]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_add (hIs _) (hIs _)
  rw [hgm]
  simp only [hresp, Finset.sum_sub_distrib]
  have hs1 : ∀ c : TorusBond n, G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) c) =
      G.expectation ∅ (chartMean G (scoreCase G.coarse c)) := fun c => rfl
  simp only [hs1]
  ring
end Core
end GasMeanOfResponse
open GasMeanOfResponse in
theorem coldStepIntegralEqGasMean_holds (hM : caseMeanEqGasMeanStatement)
    (hS : ResponseInTheExpansion.siteScoreHasIntegrableMajorant) (hB : gasIntegrandMeasurableStatement)
    (hI : CaseMassEqGasMass) (hCf : GasConfigIsAdmissibleSetting) (hW : GasIsActivityBounded)
    (hMs : SettingMassEqIntegral) (hCL : ActivityConditionalLawsStatement) (hBo : CaseIntegrandMeasurable)
    (hK : BondKernelProperties) (hsb : BondScoreProperties) : coldStepIntegralEqGasMean := by
  obtain ⟨r₁, p₁, g₁⟩ := hM
  obtain ⟨r₂, p₂, g₂⟩ := hS
  obtain ⟨r₃, p₃, g₃⟩ := hW
  obtain ⟨r₄, p₄, g₄⟩ := hMs
  refine ⟨fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c)),
    fun c => lt_min (lt_min (p₁ c) (p₂ c)) (lt_min (p₃ c) (p₄ c)), fun T hD hrt K => ?_⟩
  obtain ⟨y₁, G₁⟩ := g₁ T hD (hrt.trans ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨y₂, G₂⟩ := g₂ T hD (hrt.trans ((min_le_left _ _).trans (min_le_right _ _))) K
  obtain ⟨y₃, G₃⟩ := g₃ T hD (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₄, G₄⟩ := g₄ T hD (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨y₅, G₅⟩ := hB T hD
  obtain ⟨y₆, G₆⟩ := hI T hD
  obtain ⟨y₇, G₇⟩ := hCf T hD
  obtain ⟨y₈, G₈⟩ := hBo T hD
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (max (max y₅ y₆) (max y₇ y₈)) (max T.floorMin (200 * T.B))),
    fun y hy R A hKA hAt n _ G hG Y h => ?_⟩
  have ha := (le_max_left _ _).trans hy
  have hb := (le_max_right _ _).trans hy
  have hc := (le_max_left _ _).trans hb
  have hd := (le_max_right _ _).trans hb
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans ha)
  have hy2 : y₂ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans ha)
  have hy3 : y₃ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ha)
  have hy4 : y₄ ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans ha)
  have hy5 : y₅ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hy6 : y₆ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hy7 : y₇ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hy8 : y₈ ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hd
  have hyB : 200 * T.B ≤ y := (le_max_right _ _).trans hd
  have hR := hAt.onFamily
  have hx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    have h2 := hR.le_coupling
    linarith
  have hfit : R.params.Admissible := hR.params_eq ▸ hD.fits y hy0
  have hrow : R.HasExpansions := hR.isStep.1
  have hn₀q : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hσq : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hn : R.params.n₀ ≤ n := by
    rcases hG with g | g
    · exact g.n₀_le
    · exact le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))) g.isBlockSide.2
  have hnT : T.n₀ ≤ n := hn₀q ▸ hn
  have hρ : 0 < R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [hσq]
    rw [e, hR.barrierFn_eq]
    exact hD.cut
  have hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate) :=
    G₃ y hy3 R hR hx n G hG _
  have hset := G₇ y hy7 R hR hx n G hG
  have hmassS : ∀ σ, G.pairConstraint.IsAdmissible σ →
      Integrable (fun η => (configSetting G σ).cutoffProduct η * Real.exp (-(configSetting G σ).potential η)) ∧
      0 < ∫ η, (configSetting G σ).cutoffProduct η * Real.exp (-(configSetting G σ).potential η) ∧
      settingMass (configSetting G σ) =
        ENNReal.ofReal (∫ η, (configSetting G σ).cutoffProduct η * Real.exp (-(configSetting G σ).potential η)) :=
    fun σ hs => G₄ y hy4 R hR n hnT _ (hset σ hs)
  have hf : GasHypotheses G (G.spinActivity T.gasRate) :=
    { weight := hw
      prob := (hCL _ _ G.pairConstraint (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate) hw).1
      setting := hset
      density_int := fun σ hs => (hmassS σ hs).1
      density_pos := fun σ hs => (hmassS σ hs).2.1
      mass := fun σ hs => (hmassS σ hs).2.2
      borel := G₅ y hy5 R hR hx n G hG }
  have hAr := hAt.admissible
  have hC₀ : 0 ≤ A.responseParams.C₀ := by
    have h1 := hAr.params_admissible.C₀_eq
    have h2 := hAr.params_admissible.N₀_nonneg
    have h3 := hAr.params_admissible.Kc_ge
    have h4 := hfit.a_ge
    rw [h1]
    linarith
  refine caseResponse_integrable_and_mean hrow hfit hn hρ hcut hAr.bounds hC₀ hAr.price.nonneg hK hsb hf
    (G₂ y hy2 R A hKA hAt n G hG) ?_ ?_ ?_ Y h
  · exact fun F hF bad Yt b => (G₈ y hy8 R hR hx n G hG).1 F hF bad Yt b
  · exact fun F hF => G₆ y hy6 R hR hx n G hG ∅ F hF (G₅ y hy5 R hR hx n G hG F hF)
  · exact fun F hm hg hi => ((G₁ y hy1 R hR hx n G hG).2 F hm hg hi).2
end WeightedResponses
end YangMills.Construction
end
