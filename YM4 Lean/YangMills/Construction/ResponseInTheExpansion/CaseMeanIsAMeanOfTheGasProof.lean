import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheStateProof
import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.ConvexityOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfACaseAtAStep
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsAGas
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAGround
import YangMills.Construction.ResponseInTheExpansion.CaseMeanIsAMeanOfTheGas
import YangMills.Construction.ResponseInTheExpansion.GasIntegrandIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open StepGas StepSettings TorusLumps TorusFields StepCosts RenormalizationStepParameters LumpContours ColdStepAtMirrorFrames
  BlockZones BlockAverages Dobrushin
namespace CaseMeanProof
section Parts
private theorem integral_integral_eq_posPart_sub_negPart {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {g : X → Y → ℝ} (hg : Integrable (fun p : X × Y => g p.1 p.2) (μ.prod ν)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y) ∂ν ∂μ) ≠ ⊤ ∧ (∫⁻ x, ∫⁻ y, ENNReal.ofReal (-g x y) ∂ν ∂μ) ≠ ⊤ ∧
      ∫ x, ∫ y, g x y ∂ν ∂μ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y) ∂ν ∂μ).toReal -
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal (-g x y) ∂ν ∂μ).toReal := by
  have hpos : AEMeasurable (fun p : X × Y => ENNReal.ofReal (g p.1 p.2)) (μ.prod ν) :=
    hg.1.aemeasurable.ennreal_ofReal
  have hneg : AEMeasurable (fun p : X × Y => ENNReal.ofReal (-g p.1 p.2)) (μ.prod ν) :=
    hg.1.aemeasurable.neg.ennreal_ofReal
  have epos := lintegral_prod _ hpos
  have eneg := lintegral_prod _ hneg
  simp only at epos eneg
  rw [← epos, ← eneg]
  refine ⟨hg.lintegral_lt_top.ne, hg.neg.lintegral_lt_top.ne, ?_⟩
  rw [← integral_prod (fun p : X × Y => g p.1 p.2) hg]
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg
private theorem integral_mul_density_eq_parts {E : Type*} [MeasurableSpace E] {μ : Measure E} {f d : E → ℝ}
    (hf : Measurable f)
    (hd : AEStronglyMeasurable d μ) (hd0 : ∀ x, 0 ≤ d x)
    (hp : ∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (d x) ∂μ ≠ ⊤)
    (hn : ∫⁻ x, ENNReal.ofReal (-f x) * ENNReal.ofReal (d x) ∂μ ≠ ⊤) :
    ∫ x, f x * d x ∂μ = (∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (d x) ∂μ).toReal -
      (∫⁻ x, ENNReal.ofReal (-f x) * ENNReal.ofReal (d x) ∂μ).toReal := by
  have epos : ∀ x, ENNReal.ofReal (f x * d x) = ENNReal.ofReal (f x) * ENNReal.ofReal (d x) := fun x =>
    ENNReal.ofReal_mul' (hd0 x)
  have eneg : ∀ x, ENNReal.ofReal (-(f x * d x)) = ENNReal.ofReal (-f x) * ENNReal.ofReal (d x) := fun x => by
    rw [← neg_mul]
    exact ENNReal.ofReal_mul' (hd0 x)
  have hm : AEStronglyMeasurable (fun x => f x * d x) μ := hf.aestronglyMeasurable.mul hd
  have hi : Integrable (fun x => f x * d x) μ := by
    refine ⟨hm, ?_⟩
    have hle : ∀ x, ‖f x * d x‖ₑ ≤ ENNReal.ofReal (f x * d x) + ENNReal.ofReal (-(f x * d x)) := by
      intro x
      rw [Real.enorm_eq_ofReal_abs]
      rcases le_total 0 (f x * d x) with h | h
      · rw [abs_of_nonneg h]
        exact le_self_add
      · rw [abs_of_nonpos h]
        exact le_add_self
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    rw [lintegral_add_left' hm.aemeasurable.ennreal_ofReal]
    simp only [epos, eneg]
    exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hp, lt_top_iff_ne_top.mpr hn⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
  simp only [epos, eneg]
end Parts
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def posPart (F : CaseFunction R n) : ClusterExpansionOfAStep.CaseFunctional R n :=
  fun W Yt ω bad b => ENNReal.ofReal (F W Yt ω bad b)
private def negate (F : CaseFunction R n) : CaseFunction R n := fun W Yt ω bad b => -F W Yt ω bad b
section Cases
variable (G : GasGround R n) (F : CaseFunction R n)
private theorem caseIntegrand_posPart (hw : ∀ (bad : Finset (TorusBond (n * R.params.side)))
      (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
      (ν : G.state.unlabelled Yt → R.labels.Ω),
      IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt →
      0 ≤ stepWeight R G.cut G.coarse (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω) :
    G.caseIntegrand (posPart F) bad Yt b W ν =
      ENNReal.ofReal (caseTerm R G.cut G.coarse G.state F bad Yt b W ν) := by
  classical
  unfold GasGround.caseIntegrand caseTerm posPart
  by_cases h : IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state
  · rw [if_pos h, if_pos h, ENNReal.ofReal_mul' (hw bad Yt b W ν h.1)]
  · rw [if_neg h, if_neg h]
    simp
private theorem caseTerm_negate (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
    (ν : G.state.unlabelled Yt → R.labels.Ω) :
    caseTerm R G.cut G.coarse G.state (negate F) bad Yt b W ν =
      -caseTerm R G.cut G.coarse G.state F bad Yt b W ν := by
  classical
  unfold caseTerm negate
  by_cases h : IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state
  · rw [if_pos h, if_pos h, neg_mul]
  · rw [if_neg h, if_neg h, neg_zero]
private theorem caseMass_empty_eq (X : ClusterExpansionOfAStep.CaseFunctional R n) :
    G.caseMass ∅ X = ∑ bad ∈ (markedBonds R G.cut).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n, G.caseIntegral X bad Yt b := by
  classical
  unfold GasGround.caseMass
  refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => ?_
  have hoff : G.CaseAvoids ∅ bad Yt := ⟨fun _ _ _ => by simp, fun _ _ _ => by simp⟩
  exact if_pos hoff
abbrev _root_.YangMills.SharedProofs.p25367 := @caseMass_empty_eq
private theorem caseIntegral_eq_parts (hw : ∀ (bad : Finset (TorusBond (n * R.params.side)))
      (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
      (ν : G.state.unlabelled Yt → R.labels.Ω),
      IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt →
      0 ≤ stepWeight R G.cut G.coarse (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b)
    (hI : CaseIntegrable R G.cut G.coarse G.state F) :
    G.caseMass ∅ (posPart F) ≠ ⊤ ∧ G.caseMass ∅ (posPart (negate F)) ≠ ⊤ ∧
      caseIntegral R G.cut G.coarse G.state F =
        (G.caseMass ∅ (posPart F)).toReal - (G.caseMass ∅ (posPart (negate F))).toReal := by
  classical
  have key : ∀ bad ∈ (markedBonds R G.cut).powerset, ∀ (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      G.caseIntegral (posPart F) bad Yt b ≠ ⊤ ∧ G.caseIntegral (posPart (negate F)) bad Yt b ≠ ⊤ ∧
        ∫ W, ∫ ν : G.state.unlabelled Yt → R.labels.Ω, caseTerm R G.cut G.coarse G.state F bad Yt b W ν
            ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
          (G.caseIntegral (posPart F) bad Yt b).toReal -
            (G.caseIntegral (posPart (negate F)) bad Yt b).toReal := by
    intro bad hbad Yt b
    have epos : G.caseIntegral (posPart F) bad Yt b = ∫⁻ W, ∫⁻ ν : G.state.unlabelled Yt → R.labels.Ω,
        ENNReal.ofReal (caseTerm R G.cut G.coarse G.state F bad Yt b W ν)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
      unfold GasGround.caseIntegral
      simp only [caseIntegrand_posPart G F hw]
    have eneg : G.caseIntegral (posPart (negate F)) bad Yt b = ∫⁻ W, ∫⁻ ν : G.state.unlabelled Yt → R.labels.Ω,
        ENNReal.ofReal (-caseTerm R G.cut G.coarse G.state F bad Yt b W ν)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
      unfold GasGround.caseIntegral
      simp only [caseIntegrand_posPart G (negate F) hw, caseTerm_negate]
    rw [epos, eneg]
    exact integral_integral_eq_posPart_sub_negPart
      (g := fun W ν => caseTerm R G.cut G.coarse G.state F bad Yt b W ν) (hI bad hbad Yt b)
  refine ⟨?_, ?_, ?_⟩
  · rw [caseMass_empty_eq]
    exact ENNReal.sum_ne_top.mpr fun bad hbad => ENNReal.sum_ne_top.mpr fun Yt _ =>
      ENNReal.sum_ne_top.mpr fun b _ => (key bad hbad Yt b).1
  · rw [caseMass_empty_eq]
    exact ENNReal.sum_ne_top.mpr fun bad hbad => ENNReal.sum_ne_top.mpr fun Yt _ =>
      ENNReal.sum_ne_top.mpr fun b _ => (key bad hbad Yt b).2.1
  · rw [caseMass_empty_eq, caseMass_empty_eq]
    have hs : ∀ X : ClusterExpansionOfAStep.CaseFunctional R n,
        (∀ bad ∈ (markedBonds R G.cut).powerset, ∀ Yt b, G.caseIntegral X bad Yt b ≠ ⊤) →
        (∑ bad ∈ (markedBonds R G.cut).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
          ∑ b : BaseChoice R.params.side n, G.caseIntegral X bad Yt b).toReal =
        ∑ bad ∈ (markedBonds R G.cut).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
          ∑ b : BaseChoice R.params.side n, (G.caseIntegral X bad Yt b).toReal := by
      intro X hX
      rw [ENNReal.toReal_sum fun bad hbad => ENNReal.sum_ne_top.mpr fun Yt _ =>
        ENNReal.sum_ne_top.mpr fun b _ => hX bad hbad Yt b]
      refine Finset.sum_congr rfl fun bad hbad => ?_
      rw [ENNReal.toReal_sum fun Yt _ => ENNReal.sum_ne_top.mpr fun b _ => hX bad hbad Yt b]
      refine Finset.sum_congr rfl fun Yt _ => ?_
      rw [ENNReal.toReal_sum fun b _ => hX bad hbad Yt b]
    rw [hs _ fun bad hbad Yt b => (key bad hbad Yt b).1, hs _ fun bad hbad Yt b => (key bad hbad Yt b).2.1]
    simp only [← Finset.sum_sub_distrib]
    unfold caseIntegral
    refine Finset.sum_congr rfl fun bad hbad => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
    exact (key bad hbad Yt b).2.2
end Cases
section Gas
variable (G : GasGround R n) (F : CaseFunction R n)
private theorem integral_chartDensity (σ : G.Config) (ha : G.pairConstraint.IsAdmissible σ)
    (hd : AEStronglyMeasurable (chartDensity (configSetting G σ)) volume)
    (hd0 : ∀ η, 0 ≤ chartDensity (configSetting G σ) η) :
    ∫ η, chartDensity (configSetting G σ) η = G.weight σ := by
  have hw : G.weight σ = (settingMass (configSetting G σ)).toReal := if_pos ha
  rw [hw, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hd0) hd]
  rfl
private theorem ae_admissible_gibbsLaw {P : G.Config → Prop}
    (hdens : Measurable (G.pairConstraint.weightDensity G.weight))
    (hP : ∀ σ, G.pairConstraint.IsAdmissible σ → P σ) :
    ∀ᵐ σ ∂G.gibbsLaw ∅, G.pairConstraint.IsAdmissible σ ∧ P σ := by
  classical
  have hlaw : G.gibbsLaw ∅ = (G.partitionFunction ∅)⁻¹ •
      (Measure.pi (G.referenceMeasure ∅)).withDensity (G.pairConstraint.weightDensity G.weight) := rfl
  rw [hlaw]
  refine Measure.ae_smul_measure ?_ _
  rw [ae_withDensity_iff hdens]
  refine Filter.Eventually.of_forall fun σ h => ?_
  have ha : G.pairConstraint.IsAdmissible σ := by
    by_contra hn
    exact h (if_neg hn)
  exact ⟨ha, hP σ ha⟩
private theorem weightDensity_mul_weightedMean (σ : G.Config) (ha : G.pairConstraint.IsAdmissible σ)
    (hpos : 0 < G.weight σ)
    (hF : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b)
    (hd : AEStronglyMeasurable (chartDensity (configSetting G σ)) volume)
    (hd0 : ∀ η, 0 ≤ chartDensity (configSetting G σ) η)
    (hp : G.gasIntegrand (posPart F) σ ≠ ⊤) (hn : G.gasIntegrand (posPart (negate F)) σ ≠ ⊤) :
    (G.pairConstraint.weightDensity G.weight σ).toReal *
        weightedMean (chartDensity (configSetting G σ)) (fun η =>
        F ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
          (G.badBondsOf σ) (configSetting G σ).bases) =
      (G.gasIntegrand (posPart F) σ).toReal - (G.gasIntegrand (posPart (negate F)) σ).toReal := by
  classical
  set s := configSetting G σ with hs
  have hfm : Measurable fun η => F (s.field η) s.support s.labelling (G.badBondsOf σ) s.bases :=
    (hF s.support (G.badBondsOf σ) s.bases).comp
      ((ClusterExpansionOfAStep.ChartSetting.measurable_field s).prodMk measurable_const)
  have epos : G.gasIntegrand (posPart F) σ =
      ∫⁻ η, ENNReal.ofReal (F (s.field η) s.support s.labelling (G.badBondsOf σ) s.bases) *
      ENNReal.ofReal (chartDensity s η) := by
    unfold GasGround.gasIntegrand
    rw [if_pos ha]
    rfl
  have eneg : G.gasIntegrand (posPart (negate F)) σ =
      ∫⁻ η, ENNReal.ofReal (-F (s.field η) s.support s.labelling (G.badBondsOf σ) s.bases) *
      ENNReal.ofReal (chartDensity s η) := by
    unfold GasGround.gasIntegrand
    rw [if_pos ha]
    rfl
  have hpart := integral_mul_density_eq_parts hfm hd hd0 (epos ▸ hp) (eneg ▸ hn)
  rw [← epos, ← eneg] at hpart
  have hmass : ∫ η, chartDensity s η = G.weight σ := integral_chartDensity G σ ha hd hd0
  have hden : (G.pairConstraint.weightDensity G.weight σ).toReal = G.weight σ := by
    unfold PairConstraint.weightDensity
    rw [if_pos ha, ENNReal.toReal_ofReal hpos.le]
  rw [hden]
  unfold weightedMean
  rw [hmass, hpart, mul_div_cancel₀ _ hpos.ne']
private theorem gasExpectation_eq_parts (hdens : Measurable (G.pairConstraint.weightDensity G.weight))
    (hP : Measurable (G.gasIntegrand (posPart F))) (hN : Measurable (G.gasIntegrand (posPart (negate F))))
    (hfp : G.gasMass ∅ (posPart F) ≠ ⊤) (hfn : G.gasMass ∅ (posPart (negate F)) ≠ ⊤)
    (hpt : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → G.gasIntegrand (posPart F) σ ≠ ⊤ →
      G.gasIntegrand (posPart (negate F)) σ ≠ ⊤ →
      (G.pairConstraint.weightDensity G.weight σ).toReal *
        weightedMean (chartDensity (configSetting G σ)) (fun η =>
        F ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
          (G.badBondsOf σ) (configSetting G σ).bases) =
      (G.gasIntegrand (posPart F) σ).toReal - (G.gasIntegrand (posPart (negate F)) σ).toReal) :
    gasExpectationOfCase G F = (G.partitionFunction ∅)⁻¹.toReal *
      ((G.gasMass ∅ (posPart F)).toReal - (G.gasMass ∅ (posPart (negate F))).toReal) := by
  classical
  have hlt : ∀ᵐ σ ∂(Measure.pi (G.referenceMeasure ∅)), G.pairConstraint.weightDensity G.weight σ < ⊤ := by
    refine Filter.Eventually.of_forall fun σ => ?_
    unfold PairConstraint.weightDensity
    split_ifs
    · exact ENNReal.ofReal_lt_top
    · exact ENNReal.zero_lt_top
  have hlaw : G.gibbsLaw ∅ = (G.partitionFunction ∅)⁻¹ •
      (Measure.pi (G.referenceMeasure ∅)).withDensity (G.pairConstraint.weightDensity G.weight) := rfl
  unfold gasExpectationOfCase GasGround.expectation
  rw [hlaw, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hdens hlt, smul_eq_mul]
  congr 1
  have hip : Integrable (fun σ => (G.gasIntegrand (posPart F) σ).toReal) (Measure.pi (G.referenceMeasure ∅)) :=
    integrable_toReal_of_lintegral_ne_top hP.aemeasurable hfp
  have hin : Integrable (fun σ => (G.gasIntegrand (posPart (negate F)) σ).toReal)
      (Measure.pi (G.referenceMeasure ∅)) :=
    integrable_toReal_of_lintegral_ne_top hN.aemeasurable hfn
  have epos := integral_toReal hP.aemeasurable (ae_lt_top hP hfp)
  have eneg := integral_toReal hN.aemeasurable (ae_lt_top hN hfn)
  have ediff : (G.gasMass ∅ (posPart F)).toReal - (G.gasMass ∅ (posPart (negate F))).toReal =
      ∫ σ, ((G.gasIntegrand (posPart F) σ).toReal - (G.gasIntegrand (posPart (negate F)) σ).toReal)
        ∂(Measure.pi (G.referenceMeasure ∅)) := by
    rw [integral_sub hip hin, epos, eneg]
    rfl
  rw [ediff]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hP hfp, ae_lt_top hN hfn] with σ h1 h2
  by_cases ha : G.pairConstraint.IsAdmissible σ
  · rw [smul_eq_mul]
    exact hpt σ ha h1.ne h2.ne
  · have d0 : G.pairConstraint.weightDensity G.weight σ = 0 := if_neg ha
    have g1 : G.gasIntegrand (posPart F) σ = 0 := if_neg ha
    have g2 : G.gasIntegrand (posPart (negate F)) σ = 0 := if_neg ha
    rw [d0, g1, g2]
    simp
private theorem integrable_weightedMean (hdens : Measurable (G.pairConstraint.weightDensity G.weight))
    (hP : Measurable (G.gasIntegrand (posPart F))) (hN : Measurable (G.gasIntegrand (posPart (negate F))))
    (hfp : G.gasMass ∅ (posPart F) ≠ ⊤) (hfn : G.gasMass ∅ (posPart (negate F)) ≠ ⊤)
    (hpt : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → G.gasIntegrand (posPart F) σ ≠ ⊤ →
      G.gasIntegrand (posPart (negate F)) σ ≠ ⊤ →
      (G.pairConstraint.weightDensity G.weight σ).toReal *
        weightedMean (chartDensity (configSetting G σ)) (fun η =>
        F ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
          (G.badBondsOf σ) (configSetting G σ).bases) =
      (G.gasIntegrand (posPart F) σ).toReal - (G.gasIntegrand (posPart (negate F)) σ).toReal) :
    Integrable (fun σ => weightedMean (chartDensity (configSetting G σ)) fun η =>
      F ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
        (G.badBondsOf σ) (configSetting G σ).bases)
      (G.gibbsLaw ∅) := by
  classical
  have hlt : ∀ᵐ σ ∂(Measure.pi (G.referenceMeasure ∅)), G.pairConstraint.weightDensity G.weight σ < ⊤ := by
    refine Filter.Eventually.of_forall fun σ => ?_
    unfold PairConstraint.weightDensity
    split_ifs
    · exact ENNReal.ofReal_lt_top
    · exact ENNReal.zero_lt_top
  have hlaw : G.gibbsLaw ∅ = (G.partitionFunction ∅)⁻¹ •
      (Measure.pi (G.referenceMeasure ∅)).withDensity (G.pairConstraint.weightDensity G.weight) := rfl
  have hip : Integrable (fun σ => (G.gasIntegrand (posPart F) σ).toReal) (Measure.pi (G.referenceMeasure ∅)) :=
    integrable_toReal_of_lintegral_ne_top hP.aemeasurable hfp
  have hin : Integrable (fun σ => (G.gasIntegrand (posPart (negate F)) σ).toReal)
      (Measure.pi (G.referenceMeasure ∅)) :=
    integrable_toReal_of_lintegral_ne_top hN.aemeasurable hfn
  have hi : Integrable (fun σ => (G.pairConstraint.weightDensity G.weight σ).toReal •
      weightedMean (chartDensity (configSetting G σ))
      fun η => F ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
        (G.badBondsOf σ) (configSetting G σ).bases) (Measure.pi (G.referenceMeasure ∅)) := by
    refine (hip.sub hin).congr ?_
    filter_upwards [ae_lt_top hP hfp, ae_lt_top hN hfn] with σ h1 h2
    by_cases ha : G.pairConstraint.IsAdmissible σ
    · rw [smul_eq_mul]
      exact (hpt σ ha h1.ne h2.ne).symm
    · have d0 : G.pairConstraint.weightDensity G.weight σ = 0 := if_neg ha
      have g1 : G.gasIntegrand (posPart F) σ = 0 := if_neg ha
      have g2 : G.gasIntegrand (posPart (negate F)) σ = 0 := if_neg ha
      simp [d0, g1, g2]
  have h1 := (integrable_withDensity_iff_integrable_smul' hdens hlt).mpr hi
  rw [hlaw]
  by_cases hZ : G.partitionFunction ∅ = 0
  · have h0 : (Measure.pi (G.referenceMeasure ∅)).withDensity (G.pairConstraint.weightDensity G.weight) = 0 := by
      rw [withDensity_eq_zero_iff hdens.aemeasurable]
      exact (lintegral_eq_zero_iff hdens).mp hZ
    rw [h0, smul_zero]
    exact integrable_zero_measure
  · exact h1.smul_measure (ENNReal.inv_ne_top.mpr hZ)
end Gas
section Positive
private theorem le_clusterRange {N : ℕ} {x : ℝ} (h : (N : ℝ) ^ 100 ≤ x) : N ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem mem_baseSitesAt {F : BlockFrame} {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth}
    (hb : IsBaseChoice J₀ h b) (y : F.Cell) : b y ∈ baseSitesAt J₀ h y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseWeightZero.mem_baseSitesAt <;> assumption
private theorem stepWeight_nonneg
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (hρ : 0 < R.ballRadius)
    (hcut : IsCutoff R.ballRadius R.barrierFn) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ωt bad b := by
  classical
  unfold stepWeight
  have h1 : 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt := hr.nonneg (n * R.params.side) hside W Yt ωt hh
  have h2 : 0 ≤ baseLaw W b := by
    unfold baseLaw
    split_ifs
    · positivity
    · exact le_rfl
  have h3 : 0 ≤ ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by
    refine Finset.prod_nonneg fun c _ => ?_
    unfold bondKernel partitionFn
    exact div_nonneg (Real.exp_pos _).le (integral_nonneg fun g => (Real.exp_pos _).le)
  have h4 : 0 ≤ markProduct R C V W bad := by
    unfold markProduct
    refine Finset.prod_nonneg fun c _ => ?_
    split_ifs
    · exact sub_nonneg.mpr (ClusterExpansionOfAStep.cutoffFactor_le_one hρ hcut (norm_nonneg _))
    · exact ClusterExpansionOfAStep.cutoffFactor_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
private theorem aestronglyMeasurable_chartDensity (s : ChartSetting R n) (hcut : IsCutoff R.ballRadius R.barrierFn)
    {U : Set (FreeCoords s.free)}
    (hK : ∀ η, s.InBalls η → η ∈ U) (hu : ContinuousOn s.potential U) :
    AEStronglyMeasurable (chartDensity s) volume := by
  classical
  set K : Set (FreeCoords s.free) := Set.univ.pi fun _ => Metric.closedBall 0 R.ballRadius with hKd
  have hmemK : ∀ η, η ∈ K ↔ s.InBalls η := by
    intro η
    simp only [hKd, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right,
      ChartSetting.InBalls, ClusterExpansionOfAStep.coordNorm_eq_norm]
  have hKm : MeasurableSet K := MeasurableSet.univ_pi fun _ => measurableSet_closedBall
  have huK : ContinuousOn s.potential K := hu.mono fun η hη => hK η ((hmemK η).mp hη)
  have hcm : Measurable fun η : FreeCoords s.free => s.cutoffProduct η := by
    unfold ChartSetting.cutoffProduct
    exact Finset.measurable_prod _ fun b _ =>
      (ClusterExpansionOfAStep.measurable_cutoffFactor_coordNorm hcut).comp (measurable_pi_apply b)
  have hoff : ∀ η, η ∉ K → chartDensity s η = 0 := by
    intro η hη
    rw [hmemK] at hη
    unfold ChartSetting.InBalls at hη
    push Not at hη
    obtain ⟨b, hb⟩ := hη
    have hzero : s.cutoffProduct η = 0 := by
      unfold ChartSetting.cutoffProduct
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      unfold cutoffFactor
      rw [if_neg (not_lt.mpr hb.le)]
    simp [chartDensity, hzero]
  have h1 : AEStronglyMeasurable (fun η => Real.exp (-s.potential η)) (volume.restrict K) :=
    (Real.continuous_exp.comp_continuousOn huK.neg).aestronglyMeasurable hKm
  have hmeas : AEStronglyMeasurable (chartDensity s) (volume.restrict K) := hcm.aestronglyMeasurable.mul h1
  have e : K.indicator (chartDensity s) = chartDensity s := by
    funext η
    by_cases h : η ∈ K
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, hoff η h]
  have h2 := (aestronglyMeasurable_indicator_iff hKm).mpr hmeas
  rwa [e] at h2
private theorem coarseFactor_prod_pos (hF : ClusterExpansionOfAStep.CaseFactorProductStatement)
    (hH : CoarseHullIsHullState)
    (hRC : R.ReadsCaseTests) (hρ : 0 < R.ballRadius) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hsl : IsBlockTorusSide R.params (n * R.params.side)) (G : GasGround R n)
    (hG : G.IsHotCase) : 0 < ∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X := by
  classical
  obtain ⟨W, Yt, ωt, bad, b, hq, hh, hbad, hatt, hΦ, hmk, hbase⟩ := hG.exists_state
  have hcC := hG.cut_eq
  have hside := hG.isBlockSide
  have hY : IsHullState R.params R.nextRange G.coarse G.state.1 := by
    have h := hH R.params hRC.admissible R.range R.nextRange hRC.range_le hRC.nextRange_ge n hside.1 G.coarse bad Yt
    have e : G.state.1 = coarseHull R.params.side R.range R.nextRange bad Yt
        (thickening (2 * R.nextRange) (torusHotSites R.params G.coarse)) := by
      rw [← hq, hcC]
      rfl
    rw [e]
    exact h
  have hbs : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b := by
    by_contra hno
    apply hbase
    unfold baseLaw
    rw [if_neg]
    intro hm
    exact hno (Finset.mem_filter.mp hm).2
  have hfac := hF R hRC n hside G.coarse G.state W Yt ωt bad b hY (by rw [← hcC]; exact hbad) hh hbs
    (by rw [← hcC]; exact hq)
  rw [hfac]
  obtain ⟨Z, hZ⟩ := exists_isAdmissibleZone G (Or.inr hG)
  have hzone : ∀ y, y ∈ G.state.markedZone ↔ y ∈ Z := fun y => by
    rw [ClusterExpansionOfAStep.mem_controlRegion]
    exact hZ.recorded_iff y
  have hlab : G.state.labelSet = Yt := by
    ext z
    rw [← hq, ClusterExpansionOfAStep.mem_labelSet_coarseStateOf]
    exact ⟨fun h => h.1, fun h => ⟨h, Finset.mem_union_right _
      (parentBlock_mem_coreBlocks (hatt (Finset.mem_union_right _ h)))⟩⟩
  refine mul_pos (mul_pos ?_ ?_) ?_
  · rw [hlab]
    exact Finset.prod_pos fun Xc hXc =>
      lt_of_le_of_ne (hRC.hasExpansions.2.factor_nonneg _ hsl _ _ _ _) (hΦ Xc hXc).symm
  · refine Finset.prod_pos fun c hc => ?_
    obtain ⟨hc1, hc2⟩ := Finset.mem_inter.mp hc
    have hst : G.IsRecorded c := (hZ.bond_iff c).2
      ⟨(hzone _).1 (Finset.mem_filter.mp hc2).2.1, (hzone _).1 (Finset.mem_filter.mp hc2).2.2⟩
    have hne := hmk c (by rw [hcC]; exact hc1) hst
    by_cases hb : c ∈ bad
    · rw [if_pos hb] at hne ⊢
      exact lt_of_le_of_ne (sub_nonneg.mpr (ClusterExpansionOfAStep.cutoffFactor_le_one hρ hcut (norm_nonneg _))) hne.symm
    · rw [if_neg hb] at hne ⊢
      exact lt_of_le_of_ne (ClusterExpansionOfAStep.cutoffFactor_nonneg _) hne.symm
  · refine Finset.prod_pos fun y _ => ?_
    have hm := mem_baseSitesAt hbs (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
    have e : blockBaseWeight R.params (stepHotLumps R.params W)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
        (b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) =
        1 / ((baseSitesAt R.params.baseDepth (stepHotLumps R.params W)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)).card : ℝ) := if_pos hm
    have hc : 0 < (baseSitesAt R.params.baseDepth (stepHotLumps R.params W)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)).card :=
      Finset.card_pos.mpr ⟨_, hm⟩
    rw [e]
    positivity
end Positive
end CaseMeanProof
open CaseMeanProof in
theorem caseMean_eq_gasExpectation (hP : ClusterExpansionOfAStep.CaseMassEqGasMass)
    (hI : coarseStateGasStatement) (hW : ClusterExpansionOfAStep.GasIsActivityBounded)
    (hA : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting)
    (hC : ClusterExpansionOfAStep.SettingsUniformlyConvex) (hB : gasIntegrandMeasurableStatement)
    (hF : ClusterExpansionOfAStep.CaseFactorProductStatement)
    (hH : CoarseHullIsHullState) : caseMeanEqGasMeanStatement := by
  classical
  obtain ⟨r₁, p₁, g₁⟩ := hI
  obtain ⟨r₂, p₂, g₂⟩ := hW
  obtain ⟨r₃, p₃, g₃⟩ := hC
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)),
    fun T hD hrt => ?_⟩
  obtain ⟨y₁, I₁⟩ := g₁ T hD (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, W₁⟩ := g₂ T hD (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨Cc, y₃, _, C₁⟩ := g₃ T hD (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨y₄, P₁⟩ := hP T hD
  obtain ⟨y₅, A₁⟩ := hA T hD
  obtain ⟨y₆, B₁⟩ := hB T hD
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (max y₅ y₆)
    (max T.floorMin (2 * ((2 ^ 40 * T.side + 2 ^ 16 : ℕ) : ℝ) ^ 100))), fun y hy R hR hxx n _ G hG => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨⟨⟨hy1, hy2⟩, hy3, hy4⟩, ⟨hy5, hy6⟩, hy8, hy9⟩ := hy
  have hxy := hR.le_coupling
  have hst := hR.isStep
  have hl := hR.params_eq
  have en : R.params.n₀ = T.n₀ := by rw [hl]; rfl
  have eσ : R.params.threshold = T.threshold := by rw [hl]; rfl
  have eL : R.params.side = T.side := by rw [hl]; rfl
  have hfits : R.params.Admissible := by
    rw [hl]
    exact hD.fits y hy8
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := by
    rcases hG with h | h
    · exact h.n₀_le
    · exact le_trans (Nat.le_mul_of_pos_left _ hLpos) h.isBlockSide.2
  have hnT : T.n₀ ≤ n := en ▸ hn₀
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have hσ : 0 < R.params.threshold := by
    rw [eσ]
    exact hD.σ_pos
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    positivity
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [eσ]
    rw [e, hR.barrierFn_eq]
    exact hD.cut
  have hrow := hst.1
  have hN0 : (0 : ℝ) ≤ ((2 ^ 40 * T.side + 2 ^ 16 : ℕ) : ℝ) ^ 100 := by positivity
  have hNr : 2 ^ 40 * T.side + 2 ^ 16 ≤ R.range := le_clusterRange (by linarith)
  have hNr' : 2 ^ 40 * T.side + 2 ^ 16 ≤ R.nextRange := le_clusterRange (by linarith [hst.2.1])
  have hRC : R.ReadsCaseTests := ⟨hrow, hfits, hst.2.2, le_trans (Nat.le_add_left _ _) hNr',
    by rw [eL]; exact le_trans (Nat.le_add_right _ _) hNr⟩
  have hnL : R.params.n₀ ≤ n * R.params.side := le_trans hn₀ (Nat.le_mul_of_pos_right _ hLpos)
  have hcold : IsCold R.params.threshold (trivialField (n * R.params.side)) := by
    intro x μ ν _
    simpa [curvature, holonomy, trivialField] using hσ
  have hD0 : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) :=
    hrow.1.positive (n * R.params.side) hnL _ hcold
  have hΦ0 : 0 < ∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X := by
    rcases hG with h | h
    · rw [h.state_empty]
      simp [chainComponents]
    · exact coarseFactor_prod_pos hF hH hRC hρ hcut hside G h
  set c : ℝ≥0∞ := ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
    ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) with hcd
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr hD0).ne' (ENNReal.ofReal_pos.mpr hΦ0).ne'
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hWt := W₁ y hy2 R hR hxx n G hG fun j => j.1.Touches ∅
  have hsd : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ →
      AEStronglyMeasurable (chartDensity (configSetting G σ)) volume := fun σ ha => by
    have hs := A₁ y hy5 R hR hxx n G hG σ ha
    obtain ⟨U, _, hUK, hUc⟩ := (C₁ y hy3 R hR n hnT _ hs).1.contDiffOn_nhds
    exact aestronglyMeasurable_chartDensity _ hcut hUK hUc.continuousOn
  have hsn : ∀ (σ : G.Config) (η : FreeCoords (configSetting G σ).free),
      0 ≤ chartDensity (configSetting G σ) η :=
    fun σ η => mul_nonneg (Finset.prod_nonneg fun _ _ => ClusterExpansionOfAStep.cutoffFactor_nonneg _) (Real.exp_pos _).le
  refine ⟨ae_admissible_gibbsLaw G hWt.measurable_weightDensity fun σ ha => ?_, fun F hFm hg hint => ?_⟩
  · rw [integral_chartDensity G σ ha (hsd σ ha) (hsn σ)]
    exact hWt.pos_of_admissible σ ha
  have hwP : ClusterExpansionOfAStep.IsCaseFunctional (posPart F) :=
    ⟨fun Yt bad b => ENNReal.measurable_ofReal.comp (hFm Yt bad b),
    fun W Yt ωt bad b u hh hpos h1 h2 => congrArg ENNReal.ofReal (hg W Yt ωt bad b u ⟨hh, hpos⟩ h1 h2)⟩
  have hwN : ClusterExpansionOfAStep.IsCaseFunctional (posPart (negate F)) :=
    ⟨fun Yt bad b => ENNReal.measurable_ofReal.comp (hFm Yt bad b).neg,
    fun W Yt ωt bad b u hh hpos h1 h2 =>
      congrArg (fun v => ENNReal.ofReal (-v)) (hg W Yt ωt bad b u ⟨hh, hpos⟩ h1 h2)⟩
  have hmP := B₁ y hy6 R hR hxx n G hG (posPart F) hwP
  have hmN := B₁ y hy6 R hR hxx n G hG (posPart (negate F)) hwN
  have eP : G.caseMass ∅ (posPart F) = c * G.gasMass ∅ (posPart F) :=
    P₁ y hy4 R hR hxx n G hG ∅ (posPart F) hwP hmP
  have eN : G.caseMass ∅ (posPart (negate F)) = c * G.gasMass ∅ (posPart (negate F)) :=
    P₁ y hy4 R hR hxx n G hG ∅ (posPart (negate F)) hwN hmN
  have hw : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n)
      (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled Yt → R.labels.Ω),
      IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt →
      0 ≤ stepWeight R G.cut G.coarse (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b :=
    fun bad Yt b W ν hh => stepWeight_nonneg hrow.2 hside hρ hcut _ _ _ _ _ _ _ hh
  obtain ⟨hcP, hcN, hci⟩ := caseIntegral_eq_parts G F hw hint
  rw [eP] at hcP hci
  rw [eN] at hcN hci
  have hfp : G.gasMass ∅ (posPart F) ≠ ⊤ := fun h => hcP (by rw [h, ENNReal.mul_top hc0])
  have hfn : G.gasMass ∅ (posPart (negate F)) ≠ ⊤ := fun h => hcN (by rw [h, ENNReal.mul_top hc0])
  have hpt : ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → G.gasIntegrand (posPart F) σ ≠ ⊤ →
      G.gasIntegrand (posPart (negate F)) σ ≠ ⊤ →
      (G.pairConstraint.weightDensity G.weight σ).toReal *
        weightedMean (chartDensity (configSetting G σ)) (fun η =>
        F ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
          (G.badBondsOf σ) (configSetting G σ).bases) =
      (G.gasIntegrand (posPart F) σ).toReal - (G.gasIntegrand (posPart (negate F)) σ).toReal :=
    fun σ ha h1 h2 => weightDensity_mul_weightedMean G F σ ha (hWt.pos_of_admissible σ ha) hFm (hsd σ ha) (hsn σ) h1 h2
  refine ⟨integrable_weightedMean G F hWt.measurable_weightDensity hmP hmN hfp hfn hpt, ?_⟩
  have hgas := gasExpectation_eq_parts G F hWt.measurable_weightDensity hmP hmN hfp hfn hpt
  have hZ : coarseStateWeight R G.cut G.coarse G.state = (c * G.partitionFunction ∅).toReal := by
    unfold coarseStateWeight
    rw [(I₁ y hy1 R hR hxx n G hG).2.2.2.1]
  have hc' : c.toReal ≠ 0 := (ENNReal.toReal_pos hc0 hct).ne'
  show caseMean R G.cut G.coarse G.state F = gasExpectationOfCase G F
  rw [hgas]
  unfold caseMean
  have ht : ∀ m : ℝ≥0∞, (c * m).toReal = c.toReal * m.toReal := fun m => ENNReal.toReal_mul
  rw [hci, hZ, ht, ht, ht, ENNReal.toReal_inv, ← mul_sub, mul_div_mul_left _ _ hc', div_eq_inv_mul]
end YangMills.Construction.WeightedResponses
end
