import YangMills.Construction.ClusterExpansionOfAStep.CaseFunctionIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.FreeEnergiesOfTheFlow.FunctionsOfTheLabelsAreIntegrable
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanScoresOverTheGasProof
import YangMills.Construction.ResponseInTheExpansion.GasIntegrandIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction
open Dobrushin StepSettings StepGas RenormalizationStepParameters TorusFields TorusLumps WeightedResponses ClusterExpansionOfAStep ResponseInTheExpansion
  BlockAverages LumpContours ColdStepAtMirrorFrames
namespace FreeEnergies
variable {R : StepSetup} {n : ℕ} [NeZero n] {A : ResponseSetup R} {G : GasGround R n}
private theorem sum_spinSiteScore_le_spinScore (hs : ∀ w, 0 ≤ A.score w) (i : G.GasSpin) (v : G.SpinValue i)
    (S : Finset (TorusSite (n * R.params.side))) :
    ∑ y ∈ S, spinSiteScore A G i y v ≤ spinScore A i v := by apply _root_.YangMills.SharedProofs.p40586 <;> assumption
private def expSpinFactor (A : ResponseSetup R) (G : GasGround R n) (S : Finset (TorusSite (n * R.params.side)))
    (i : G.GasSpin) (v : G.SpinValue i) : ℝ :=
  Real.exp (∑ y ∈ S, spinSiteScore A G i y v)
private def expScoreFunctional (A : ResponseSetup R) (S : Finset (TorusSite (n * R.params.side))) :
    CaseFunctional R n :=
  fun _ Yt ωt _ _ => ENNReal.ofReal (Real.exp (scoreSumOn A S Yt ωt))
private theorem gasIntegrand_expScore_eq (hpos : ∀ σ, G.pairConstraint.IsAdmissible σ → 0 < G.weight σ)
    (S : Finset (TorusSite (n * R.params.side))) (σ : G.Config) :
    G.gasIntegrand (expScoreFunctional A S) σ =
      ENNReal.ofReal (Real.exp (scoreSumOn A S (configSetting G σ).support (configSetting G σ).labelling)) *
        G.pairConstraint.weightDensity G.weight σ := by
  classical
  unfold GasGround.gasIntegrand PairConstraint.weightDensity
  by_cases ha : G.pairConstraint.IsAdmissible σ
  · rw [if_pos ha, if_pos ha]
    have hw := hpos σ ha
    have hm : settingMass (G.settingOf (G.familyOf σ)) ≠ ⊤ := by
      intro htop
      unfold GasGround.weight at hw
      rw [if_pos ha, htop] at hw
      simp at hw
    have e : ENNReal.ofReal (G.weight σ) = settingMass (G.settingOf (G.familyOf σ)) := by
      unfold GasGround.weight
      rw [if_pos ha, ENNReal.ofReal_toReal hm]
    rw [e]
    unfold ChartSetting.settingIntegral settingMass expScoreFunctional
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [if_neg ha, if_neg ha, mul_zero]
private theorem exp_scoreSumOn_le (hs : ∀ w, 0 ≤ A.score w) (S : Finset (TorusSite (n * R.params.side)))
    (σ : G.Config) :
    Real.exp (scoreSumOn A S (configSetting G σ).support (configSetting G σ).labelling) ≤
      Real.exp (∑ y ∈ S, recordedSiteScore A G y) * ∏ i, expSpinFactor A G S i (σ i) := by
  classical
  unfold expSpinFactor
  rw [← Real.exp_sum, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  unfold scoreSumOn
  calc ∑ y ∈ S, siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y
      ≤ ∑ y ∈ S, (recordedSiteScore A G y + ∑ i, spinSiteScore A G i y (σ i)) :=
        Finset.sum_le_sum fun y _ => siteScore_configSetting_le hs σ y
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_comm]
private theorem gasMass_expScore_ne_top (hP : MeanOfProductStatement) {z : G.GasSpin → ℝ}
    (hW : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z) (hs : ∀ w, 0 ≤ A.score w)
    (hb : Measurable A.score) (S : Finset (TorusSite (n * R.params.side)))
    (hpaid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
        ENNReal.ofReal (z i) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (hP0 : G.partitionFunction ∅ ≠ 0) (hPt : G.partitionFunction ∅ ≠ ⊤) :
    G.gasMass ∅ (expScoreFunctional A S) ≠ ⊤ := by
  classical
  have hgm : ∀ i, Measurable (expSpinFactor A G S i) := fun i =>
    Real.measurable_exp.comp (Finset.measurable_sum _ fun y _ => measurable_spinSiteScore hb i y)
  have hg1 : ∀ i s, 1 ≤ expSpinFactor A G S i s := fun i s =>
    Real.one_le_exp (Finset.sum_nonneg fun y _ => spinSiteScore_nonneg hs i y s)
  have hga : ∀ i, expSpinFactor A G S i (G.pairConstraint.vacant i) = 1 := by
    intro i
    unfold expSpinFactor
    have : ∑ y ∈ S, spinSiteScore A G i y (G.pairConstraint.vacant i) = 0 :=
      Finset.sum_eq_zero fun y _ => rfl
    rw [this, Real.exp_zero]
  have hx : G.pairConstraint.HasSmallExcess (G.referenceMeasure ∅) G.weight (expSpinFactor A G S) z := by
    intro i σ hσ
    refine le_trans (lintegral_mono fun s => ?_) (hpaid i σ hσ)
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have h1 : expSpinFactor A G S i s ≤ Real.exp (spinScore A i s) :=
      Real.exp_le_exp.mpr (sum_spinSiteScore_le_spinScore hs i s S)
    linarith
  have key := hP G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) G.weight z hW
    (expSpinFactor A G S) z hgm hg1 hga hW.activity_nonneg hx
  set f : G.Config → ℝ≥0∞ := fun σ => ∏ i, ENNReal.ofReal (expSpinFactor A G S i (σ i)) with hf
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp ((hgm i).comp (measurable_pi_apply i))
  have hd := hW.measurable_weightDensity
  have hlaw : ∫⁻ σ, f σ ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) =
      (G.partitionFunction ∅)⁻¹ *
        ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ * f σ ∂Measure.pi (G.referenceMeasure ∅) := by
    unfold PairConstraint.gibbsLaw
    rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hd hfm]
    rfl
  have hbig : ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ * f σ ∂Measure.pi (G.referenceMeasure ∅) =
      G.partitionFunction ∅ * ∫⁻ σ, f σ ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) := by
    rw [hlaw, ← mul_assoc, ENNReal.mul_inv_cancel hP0 hPt, one_mul]
  set c : ℝ := Real.exp (∑ y ∈ S, recordedSiteScore A G y) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hpw : ∀ σ, G.gasIntegrand (expScoreFunctional A S) σ ≤
      ENNReal.ofReal c * (G.pairConstraint.weightDensity G.weight σ * f σ) := by
    intro σ
    rw [gasIntegrand_expScore_eq hW.pos_of_admissible S σ]
    have e1 : ENNReal.ofReal (Real.exp (scoreSumOn A S (configSetting G σ).support
        (configSetting G σ).labelling)) ≤ ENNReal.ofReal c * f σ := by
      simp only [hf]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => le_trans zero_le_one (hg1 i _)),
        ← ENNReal.ofReal_mul hc0]
      exact ENNReal.ofReal_le_ofReal (exp_scoreSumOn_le hs S σ)
    calc _ ≤ ENNReal.ofReal c * f σ * G.pairConstraint.weightDensity G.weight σ := by gcongr
      _ = _ := by ring
  have hle : G.gasMass ∅ (expScoreFunctional A S) ≤
      ENNReal.ofReal c * (G.partitionFunction ∅ * ENNReal.ofReal (∏ i, (1 + z i))) := by
    unfold GasGround.gasMass
    calc _ ≤ ∫⁻ σ, ENNReal.ofReal c * (G.pairConstraint.weightDensity G.weight σ * f σ)
            ∂Measure.pi (G.referenceMeasure ∅) :=
          lintegral_mono hpw
      _ = ENNReal.ofReal c *
            ∫⁻ σ, G.pairConstraint.weightDensity G.weight σ * f σ ∂Measure.pi (G.referenceMeasure ∅) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal c * (G.partitionFunction ∅ *
            ∫⁻ σ, f σ ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight)) := by rw [hbig]
      _ ≤ _ := by gcongr
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hPt ENNReal.ofReal_ne_top)) hle
omit [NeZero n] in
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by
  refine measurable_pi_iff.mpr fun z => ?_
  unfold CoarseState.fillLabels
  split
  · exact measurable_const
  · exact measurable_pi_apply _
private theorem caseIntegral_le_caseMass (F : CaseFunctional R n) {bad : Finset (TorusBond (n * R.params.side))}
    (hbad : bad ∈ (markedBonds R G.cut).powerset) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : StepCosts.BaseChoice R.params.side n) :
    G.caseIntegral F bad Yt b ≤ G.caseMass ∅ F := by
  classical
  have hoff : G.CaseAvoids ∅ bad Yt := ⟨fun _ _ _ => by simp, fun _ _ _ => by simp⟩
  unfold GasGround.caseMass
  refine le_trans ?_ (Finset.single_le_sum (f := fun bad => ∑ Yt : Finset (TorusSite (n * R.params.side)),
    if G.CaseAvoids ∅ bad Yt then ∑ b : StepCosts.BaseChoice R.params.side n, G.caseIntegral F bad Yt b else 0)
    (fun _ _ => zero_le) hbad)
  refine le_trans ?_ (Finset.single_le_sum (f := fun Yt =>
    if G.CaseAvoids ∅ bad Yt then ∑ b : StepCosts.BaseChoice R.params.side n, G.caseIntegral F bad Yt b else 0)
    (fun _ _ => zero_le) (Finset.mem_univ Yt))
  simp only [if_pos hoff]
  exact Finset.single_le_sum (f := fun b => G.caseIntegral F bad Yt b) (fun _ _ => zero_le) (Finset.mem_univ b)
abbrev _root_.YangMills.SharedProofs.p5707 := @caseIntegral_le_caseMass
private theorem caseIntegrable_of_abs_le_exp (S : Finset (TorusSite (n * R.params.side)))
    (hBo : ∀ F : CaseFunctional R n, IsCaseFunctional F → ∀ (bad : Finset (TorusBond (n * R.params.side)))
      (Yt : Finset (TorusSite (n * R.params.side))) (b : StepCosts.BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
        G.caseIntegrand F bad Yt b p.1 p.2)
    (hF : IsCaseFunctional (expScoreFunctional A S : CaseFunctional R n))
    (hfin : G.caseMass ∅ (expScoreFunctional A S) ≠ ⊤)
    (hw : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : StepCosts.BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
      (ν : G.state.unlabelled Yt → R.labels.Ω),
      IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt →
      0 ≤ stepWeight R G.cut G.coarse (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b)
    (h : (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ) (hm : ∀ Yt, Measurable (h Yt))
    (hb : ∀ Yt ωt, |h Yt ωt| ≤ Real.exp (scoreSumOn A S Yt ωt)) :
    CaseIntegrable R G.cut G.coarse G.state fun _ Yt ωt _ _ => h Yt ωt := by
  classical
  intro bad hbad Yt b
  set one : CaseFunctional R n := fun _ _ _ _ _ => 1 with hone
  have hOne : IsCaseFunctional one := ⟨fun _ _ _ => measurable_const, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  have heq : ∀ W ν, caseTerm R G.cut G.coarse G.state (fun _ Yt ωt _ _ => h Yt ωt) bad Yt b W ν =
      h Yt (G.state.fillLabels Yt ν) * (G.caseIntegrand one bad Yt b W ν).toReal := by
    intro W ν
    unfold caseTerm GasGround.caseIntegrand
    split_ifs with hc
    · simp only [hone, one_mul]
      rw [ENNReal.toReal_ofReal (hw bad Yt b W ν hc.1)]
    · simp
  have hmeas : Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
      caseTerm R G.cut G.coarse G.state (fun _ Yt ωt _ _ => h Yt ωt) bad Yt b p.1 p.2 := by
    simp only [heq]
    exact ((hm Yt).comp ((measurable_fillLabels G.state Yt).comp measurable_snd)).mul
      (hBo one hOne bad Yt b).ennreal_toReal
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  show ∫⁻ p, ‖caseTerm R G.cut G.coarse G.state (fun _ Yt ωt _ _ => h Yt ωt) bad Yt b p.1 p.2‖ₑ
    ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) < ⊤
  have hle : ∀ p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω),
      ‖caseTerm R G.cut G.coarse G.state (fun _ Yt ωt _ _ => h Yt ωt) bad Yt b p.1 p.2‖ₑ ≤
        G.caseIntegrand (expScoreFunctional A S) bad Yt b p.1 p.2 := by
    intro p
    unfold caseTerm GasGround.caseIntegrand
    split_ifs with hc
    · have h0 := hw bad Yt b p.1 p.2 hc.1
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg h0, ENNReal.ofReal_mul (abs_nonneg _)]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hb _ _)) le_rfl
    · simp
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_prod _ (hBo _ hF bad Yt b).aemeasurable]
  exact lt_of_le_of_lt (caseIntegral_le_caseMass (G := G) (expScoreFunctional A S) hbad Yt b) hfin.lt_top
theorem labelFunctionsIntegrable_proof (hS : clusterScoreIntegralBound) (hW : GasIsActivityBounded)
    (hG : CaseMassEqGasMass) (hP : MeanOfProductStatement)
    (hCL : ActivityConditionalLawsStatement) (hB : CaseIntegrandMeasurable)
    (hI : gasIntegrandMeasurableStatement) : labelFunctionsIntegrableStatement := by
  classical
  obtain ⟨r₁, p₁, hS⟩ := hS
  obtain ⟨r₂, p₂, hW⟩ := hW
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (p₁ c) (p₂ c), fun T hT hT' K => ?_⟩
  obtain ⟨yS, hS⟩ := hS T hT (hT'.trans (min_le_left _ _)) K
  obtain ⟨yW, hW⟩ := hW T hT (hT'.trans (min_le_right _ _))
  obtain ⟨yG, hG⟩ := hG T hT
  obtain ⟨yB, hB⟩ := hB T hT
  obtain ⟨yI, hI⟩ := hI T hT
  refine ⟨max (max (max yS yW) (max yG yB)) (max yI (200 * T.B)),
    fun y hy R A hK hTab n _ G hG₀ S h hm hb => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨⟨⟨hy1, hy2⟩, hy3, hy4⟩, hy5, hy6⟩ := hy
  have hOn := hTab.onFamily
  have hxy : y ≤ R.coupling := hOn.le_coupling
  have hx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have := (abs_le.mp hTab.abs_sub_le).2
    linarith
  have hst := hOn.isStep
  have hl := hOn.params_eq
  have eσ : R.params.threshold = T.threshold := by rw [hl]; rfl
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := by
    rcases hG₀ with h | h
    · exact h.n₀_le
    · exact le_trans (Nat.le_mul_of_pos_left _ hLpos) h.isBlockSide.2
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have hσ : 0 < R.params.threshold := by
    rw [eσ]
    exact hT.σ_pos
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    positivity
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [eσ]
    rw [e, hOn.barrierFn_eq]
    exact hT.cut
  have hw : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : StepCosts.BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
      (ν : G.state.unlabelled Yt → R.labels.Ω),
      IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt →
      0 ≤ stepWeight R G.cut G.coarse (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b := by
    intro bad Yt b W ν hh
    unfold stepWeight
    have h1 : 0 ≤ R.labelWeight (n * R.params.side) (G.state.fieldWithStoredLinks W) Yt
        (G.state.fillLabels Yt ν) :=
      hst.1.2.nonneg (n * R.params.side) hside _ Yt _ hh
    have h2 : 0 ≤ baseLaw (R := R) (G.state.fieldWithStoredLinks W) b := by
      unfold baseLaw
      split_ifs
      · positivity
      · exact le_rfl
    have h3 : 0 ≤ ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling
          (readAtLevel (stepBlockFrame R.params.side n) 0 (G.state.fieldWithStoredLinks W))
          (readAtLevel (stepBlockFrame R.params.side n) 1 G.coarse) b c := by
      refine Finset.prod_nonneg fun c _ => ?_
      unfold bondKernel partitionFn
      exact div_nonneg (Real.exp_pos _).le (integral_nonneg fun g => (Real.exp_pos _).le)
    have h4 : 0 ≤ markProduct R G.cut G.coarse (G.state.fieldWithStoredLinks W) bad := by
      unfold markProduct
      refine Finset.prod_nonneg fun c _ => ?_
      split_ifs
      · exact sub_nonneg.mpr (ClusterExpansionOfAStep.cutoffFactor_le_one hρ hcut (norm_nonneg _))
      · exact cutoffFactor_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have hprice := hTab.admissible.price
  have hs := hprice.nonneg
  have hsb := hprice.borel
  have hWt : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate) :=
    hW y hy2 R hOn hx n G hG₀ fun j => j.1.Touches ∅
  have hprob : IsProbabilityMeasure (G.gibbsLaw ∅) := (hCL _ _ _ _ _ _ hWt).1
  have elaw : G.gibbsLaw ∅ = (G.partitionFunction ∅)⁻¹ •
      (Measure.pi (G.referenceMeasure ∅)).withDensity (G.pairConstraint.weightDensity G.weight) := rfl
  have hPt : G.partitionFunction ∅ ≠ ⊤ := by
    intro h
    have h0 : G.gibbsLaw ∅ = 0 := by
      rw [elaw, h, ENNReal.inv_top, zero_smul]
    exact IsProbabilityMeasure.ne_zero (G.gibbsLaw ∅) h0
  have hP0 : G.partitionFunction ∅ ≠ 0 := by
    intro h
    have h1 : (Measure.pi (G.referenceMeasure ∅)).withDensity (G.pairConstraint.weightDensity G.weight) = 0 := by
      rw [← Measure.measure_univ_eq_zero, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact h
    have h0 : G.gibbsLaw ∅ = 0 := by
      rw [elaw, h1, smul_zero]
    exact IsProbabilityMeasure.ne_zero (G.gibbsLaw ∅) h0
  have hFw : IsCaseFunctional (expScoreFunctional A S : CaseFunctional R n) := by
    refine ⟨fun Yt _ _ => ?_, ?_⟩
    · have hsum : Measurable fun ωt : Yt → R.labels.Ω => scoreSumOn A S Yt ωt := by
        unfold scoreSumOn
        refine Finset.measurable_sum _ fun y _ => ?_
        unfold siteScore
        by_cases hy : y ∈ Yt
        · simp only [dif_pos hy]
          exact hsb.comp (measurable_pi_apply _)
        · simp only [dif_neg hy]
          exact measurable_const
      exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hsum.comp measurable_snd))
    · intro W Yt ωt bad bs u _ _ _ _
      have e1 : scoreSumOn A S Yt (R.labels.act Yt u ωt) = scoreSumOn A S Yt ωt := by
        unfold scoreSumOn
        refine Finset.sum_congr rfl fun y _ => ?_
        unfold siteScore
        by_cases hy : y ∈ Yt
        · rw [dif_pos hy, dif_pos hy]
          exact hprice.gauge (n * R.params.side) Yt u ωt ⟨y, hy⟩
        · rw [dif_neg hy, dif_neg hy]
      simp only [expScoreFunctional, e1]
  have hgas : G.gasMass ∅ (expScoreFunctional A S) ≠ ⊤ :=
    gasMass_expScore_ne_top hP hWt hs hsb S (fun i σ hσ => hS y hy1 R A hK hTab n G hG₀ i σ hσ) hP0 hPt
  have hmass := hG y hy3 R hOn hx n G hG₀ ∅ _ hFw (hI y hy5 R hOn hx n G hG₀ _ hFw)
  have hfin : G.caseMass ∅ (expScoreFunctional A S) ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hgas
  exact caseIntegrable_of_abs_le_exp S (hB y hy4 R hOn hx n G hG₀).1 hFw hfin hw h hm hb
end FreeEnergies
end YangMills.Construction
end
