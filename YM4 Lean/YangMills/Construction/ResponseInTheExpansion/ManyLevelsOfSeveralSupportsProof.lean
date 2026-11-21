import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.StateOverAColdField
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ResponseInTheExpansion.LevelsFormStates
import YangMills.Construction.ResponseInTheExpansion.MajorantsOfAStep
import YangMills.Construction.ResponseInTheExpansion.LevelsOfAFlow
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
import YangMills.Construction.ResponseInTheExpansion.MomentAlongIsBorel
import YangMills.Construction.ResponseInTheExpansion.OneStepOfSeveralSupports
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParametersProof
set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open RenormalizationStepParameters StepSettings TorusLumps TorusFields WeightedResponses ClusterExpansionOfAStep BlockAverages
def severalSupportsMomentStatement : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ (y₀ : ℝ) (C : ℕ → ℝ), (∀ p, 0 ≤ C p) ∧ ∀ (y β : ℝ)
      (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
      (z₀ : StageWithResponse (T.stepParameters y)), y₀ ≤ y → IsInitialStage T y β z₀ → ∀ s : ℕ,
      StagesOnFlowUpTo T K y β hL z₀ s →
      ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (T.stepParameters y) n → ∀ {ι : Type} (I : Finset ι) (D : ℕ → ℕ)
        (f : ι → StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n),
        (∀ i ∈ I, weightNorm (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth (f i) ≤ 1) →
        SeparatedAlong hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ I D s n f →
        ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → (flowStages T y β hL z₀ s).1.labels.Ω),
          IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ s).1.coupling
            (flowStages T y β hL z₀ s).1.labelWeight W Y ω →
          |jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n I f W Y ω -
              ∏ i ∈ I, supportResponseTotal (flowStages T y β hL z₀ s).2 (f i) W Y ω| ≤
            momentError hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ T.gasRate C D s n I f *
              ∏ i ∈ I, meanSiteScore (flowStages T y β hL z₀ s).2.score
                (weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n (f i)) Y ω
end ResponseInTheExpansion
end YangMills.Construction
end

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings TorusLumps TorusFields StepGas WeightedResponses RenormalizationStepParameters StepCosts BlockAverages
namespace MultiScaleMoments
section Calculus
variable {R : StepSetup} {n : ℕ} [NeZero n] {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
structure StepWeightsNonneg (R : StepSetup) (n : ℕ) [NeZero n] : Prop where
  labelWeight_nonneg : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω), IsHullState R.params R.range W Yt →
    0 ≤ R.labelWeight (n * R.params.side) W Yt ωt
  factor_nonneg : ∀ (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
    0 ≤ baseLaw W b * (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) * markProduct R C V W bad
private theorem stepWeight_eq_factor (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    stepWeight R C V W Yt ωt bad b = R.labelWeight (n * R.params.side) W Yt ωt * (baseLaw W b *
      (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) * markProduct R C V W bad) := by
  unfold stepWeight
  ring
private theorem stepWeight_nonneg_of_hull (hG : StepWeightsNonneg R n) (C : Finset (TorusSite n)) (V : TorusField n)
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (h : IsHullState R.params R.range W Yt) : 0 ≤ stepWeight R C V W Yt ωt bad b := by
  rw [stepWeight_eq_factor]
  exact mul_nonneg (hG.labelWeight_nonneg W Yt ωt h) (hG.factor_nonneg C V W bad b)
private theorem stepWeight_eq_zero_of_not_live (hG : StepWeightsNonneg R n) (C : Finset (TorusSite n)) (V : TorusField n)
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (h : IsHullState R.params R.range W Yt) (hl : ¬ IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    stepWeight R C V W Yt ωt bad b = 0 := by
  have h0 : R.labelWeight (n * R.params.side) W Yt ωt = 0 := by
    refine le_antisymm (not_lt.mp fun hp => hl ⟨h, hp⟩) (hG.labelWeight_nonneg W Yt ωt h)
  rw [stepWeight_eq_factor, h0, zero_mul]
private theorem caseTerm_add_fn (F G : CaseFunction R n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
    (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V q (fun a c d e g => F a c d e g + G a c d e g) bad Yt b W ν =
      caseTerm R C V q F bad Yt b W ν + caseTerm R C V q G bad Yt b W ν := by
  unfold caseTerm
  split_ifs <;> ring
abbrev _root_.YangMills.SharedProofs.p58450 := @caseTerm_add_fn
private theorem caseTerm_smul_fn (k : ℝ) (F : CaseFunction R n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
    (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V q (fun a c d e g => k * F a c d e g) bad Yt b W ν = k * caseTerm R C V q F bad Yt b W ν := by
  unfold caseTerm
  split_ifs <;> ring
abbrev _root_.YangMills.SharedProofs.p17898 := @caseTerm_smul_fn
private theorem caseIntegrable_add {F G : CaseFunction R n} (hF : CaseIntegrable R C V q F)
    (hG : CaseIntegrable R C V q G) :
    CaseIntegrable R C V q (fun a c d e g => F a c d e g + G a c d e g) := fun bad hbad Yt b => by
  refine ((hF bad hbad Yt b).add (hG bad hbad Yt b)).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply, caseTerm_add_fn]
private theorem caseIntegrable_const_mul (k : ℝ) {F : CaseFunction R n} (hF : CaseIntegrable R C V q F) :
    CaseIntegrable R C V q (fun a c d e g => k * F a c d e g) := fun bad hbad Yt b => by
  refine ((hF bad hbad Yt b).const_mul k).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [caseTerm_smul_fn]
private theorem caseIntegral_eq_sum_integral {F : CaseFunction R n} (hF : CaseIntegrable R C V q F) :
    caseIntegral R C V q F = ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n,
      ∫ p, caseTerm R C V q F bad Yt b p.1 p.2 ∂((fieldHaar (n * R.params.side)).prod
        (Measure.pi fun _ => R.labels.μ)) := by
  unfold caseIntegral
  refine Finset.sum_congr rfl fun bad hbad => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  exact (integral_prod _ (hF bad hbad Yt b)).symm
abbrev _root_.YangMills.SharedProofs.p48600 := @caseIntegral_eq_sum_integral
private theorem caseMean_add_fn {F G : CaseFunction R n} (hF : CaseIntegrable R C V q F)
    (hG : CaseIntegrable R C V q G) :
    caseMean R C V q (fun a c d e g => F a c d e g + G a c d e g) = caseMean R C V q F + caseMean R C V q G := by
  unfold caseMean
  rw [← add_div, caseIntegral_eq_sum_integral (caseIntegrable_add hF hG), caseIntegral_eq_sum_integral hF,
    caseIntegral_eq_sum_integral hG]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun bad hbad => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← integral_add (hF bad hbad Yt b) (hG bad hbad Yt b)]
  simp only [caseTerm_add_fn]
private theorem caseMean_const_mul_fn (k : ℝ) {F : CaseFunction R n} (hF : CaseIntegrable R C V q F) :
    caseMean R C V q (fun a c d e g => k * F a c d e g) = k * caseMean R C V q F := by
  unfold caseMean
  rw [caseIntegral_eq_sum_integral (caseIntegrable_const_mul k hF), caseIntegral_eq_sum_integral hF, ← mul_div_assoc]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun bad hbad => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← integral_const_mul]
  simp only [caseTerm_smul_fn]
private theorem caseIntegrable_sub {F G : CaseFunction R n} (hF : CaseIntegrable R C V q F)
    (hG : CaseIntegrable R C V q G) :
    CaseIntegrable R C V q (fun a c d e g => F a c d e g - G a c d e g) := by
  have h := caseIntegrable_add hF (caseIntegrable_const_mul (-1) hG)
  simpa [sub_eq_add_neg] using h
private theorem caseMean_sub_fn {F G : CaseFunction R n} (hF : CaseIntegrable R C V q F)
    (hG : CaseIntegrable R C V q G) :
    caseMean R C V q (fun a c d e g => F a c d e g - G a c d e g) = caseMean R C V q F - caseMean R C V q G := by
  have h := caseMean_add_fn hF (caseIntegrable_const_mul (-1) hG)
  rw [caseMean_const_mul_fn (-1) hG] at h
  simpa [sub_eq_add_neg] using h
private theorem caseIntegrable_sum {κ : Type} (S : Finset κ) {F : κ → CaseFunction R n}
    (hF : ∀ k ∈ S, CaseIntegrable R C V q (F k)) (hz : CaseIntegrable R C V q fun _ _ _ _ _ => 0) :
    CaseIntegrable R C V q (fun a c d e g => ∑ k ∈ S, F k a c d e g) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hz
  | insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    exact caseIntegrable_add (hF k (Finset.mem_insert_self _ _)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
private theorem caseIntegrable_zero : CaseIntegrable R C V q fun _ _ _ _ _ => 0 := fun bad hbad Yt b => by
  have : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q (fun _ _ _ _ _ => 0) bad Yt b p.1 p.2) = fun _ => 0 := by
    funext p
    unfold caseTerm
    split_ifs <;> simp
  rw [this]
  exact integrable_zero _ _ _
private theorem caseMean_zero_fn : caseMean R C V q (fun _ _ _ _ _ => 0) = 0 := by
  unfold caseMean caseIntegral
  have : ∀ bad Yt b W ν, caseTerm R C V q (fun _ _ _ _ _ => 0) bad Yt b W ν = 0 := by
    intro bad Yt b W ν
    unfold caseTerm
    split_ifs <;> simp
  simp [this]
abbrev _root_.YangMills.SharedProofs.p64354 := @caseMean_zero_fn
private theorem caseMean_sum_fn {κ : Type} (S : Finset κ) {F : κ → CaseFunction R n}
    (hF : ∀ k ∈ S, CaseIntegrable R C V q (F k)) :
    caseMean R C V q (fun a c d e g => ∑ k ∈ S, F k a c d e g) = ∑ k ∈ S, caseMean R C V q (F k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using caseMean_zero_fn
  | insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    have h1 := hF k (Finset.mem_insert_self _ _)
    have h2 : ∀ j ∈ S, CaseIntegrable R C V q (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    rw [caseMean_add_fn h1 (caseIntegrable_sum S h2 caseIntegrable_zero), ih h2]
private theorem caseTerm_congr_live (hG : StepWeightsNonneg R n) {F F' : CaseFunction R n}
    (h : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → F W Yt ωt bad b = F' W Yt ωt bad b)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V q F bad Yt b W ν = caseTerm R C V q F' bad Yt b W ν := by
  unfold caseTerm
  split_ifs with hc
  · by_cases hl : IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν)
    · rw [h _ _ _ _ _ hl]
    · rw [stepWeight_eq_zero_of_not_live hG C V _ bad b hc.1 hl, mul_zero, mul_zero]
  · rfl
private theorem caseMean_congr_live (hG : StepWeightsNonneg R n) {F F' : CaseFunction R n}
    (h : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → F W Yt ωt bad b = F' W Yt ωt bad b) :
    caseMean R C V q F = caseMean R C V q F' := by
  unfold caseMean caseIntegral
  simp only [caseTerm_congr_live hG h]
private theorem caseIntegrable_congr_live (hG : StepWeightsNonneg R n) {F F' : CaseFunction R n}
    (h : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → F W Yt ωt bad b = F' W Yt ωt bad b)
    (hF : CaseIntegrable R C V q F) : CaseIntegrable R C V q F' := fun bad hbad Yt b =>
  (hF bad hbad Yt b).congr (Filter.Eventually.of_forall fun p => caseTerm_congr_live hG h bad Yt b p.1 p.2)
private theorem abs_caseTerm_le (hG : StepWeightsNonneg R n) {F M : CaseFunction R n}
    (h : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → |F W Yt ωt bad b| ≤ M W Yt ωt bad b)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) :
    |caseTerm R C V q F bad Yt b W ν| ≤ caseTerm R C V q M bad Yt b W ν := by
  unfold caseTerm
  split_ifs with hc
  · by_cases hl : IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν)
    · have hw := stepWeight_nonneg_of_hull hG C V (q.fillLabels Yt ν) bad b hc.1
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_right (h _ _ _ _ _ hl) hw
    · rw [stepWeight_eq_zero_of_not_live hG C V _ bad b hc.1 hl, mul_zero, mul_zero, abs_zero]
  · simp
private theorem abs_caseMean_le (hG : StepWeightsNonneg R n) {F M : CaseFunction R n} (hF : CaseIntegrable R C V q F)
    (hM : CaseIntegrable R C V q M)
    (h : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → |F W Yt ωt bad b| ≤ M W Yt ωt bad b) :
    |caseMean R C V q F| ≤ caseMean R C V q M := by
  have hd : 0 ≤ coarseStateWeight R C V q := ENNReal.toReal_nonneg
  unfold caseMean
  rw [abs_div, abs_of_nonneg hd]
  refine div_le_div_of_nonneg_right ?_ hd
  rw [caseIntegral_eq_sum_integral hF, caseIntegral_eq_sum_integral hM]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun bad hbad => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun Yt _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  refine (abs_integral_le_integral_abs).trans (integral_mono (hF bad hbad Yt b).abs (hM bad hbad Yt b) fun p => ?_)
  exact abs_caseTerm_le hG h bad Yt b p.1 p.2
private theorem caseIntegral_one_eq (hG : StepWeightsNonneg R n) (h1 : CaseIntegrable R C V q fun _ _ _ _ _ => 1) :
    caseIntegral R C V q (fun _ _ _ _ _ => 1) = coarseStateWeight R C V q := by
  classical
  have hterm : ∀ bad Yt b, 0 ≤ᵐ[(fieldHaar (n * R.params.side)).prod
      (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)]
      fun p => caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2 := fun bad Yt b =>
    Filter.Eventually.of_forall fun p => by
      have := abs_caseTerm_le (q := q) (C := C) (V := V) (F := fun _ _ _ _ _ => 1) (M := fun _ _ _ _ _ => 1) hG
        (by intros; simp) bad Yt b p.1 p.2
      exact (abs_nonneg _).trans this
  have key : ∀ bad ∈ (markedBonds R C).powerset, ∀ Yt b,
      ENNReal.ofReal (∫ p, caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ))) =
      ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
        (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
            coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
          ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
    intro bad hbad Yt b
    rw [ofReal_integral_eq_lintegral_ofReal (h1 bad hbad Yt b) (hterm bad Yt b),
      lintegral_prod _ (h1 bad hbad Yt b).aestronglyMeasurable.aemeasurable.ennreal_ofReal]
    refine lintegral_congr fun W => lintegral_congr fun ν => ?_
    unfold caseTerm
    split_ifs <;> simp
  have hI : ∀ bad Yt b, 0 ≤ ∫ p, caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2
      ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := fun bad Yt b =>
    integral_nonneg_of_ae (hterm bad Yt b)
  have hfin : ∀ bad ∈ (markedBonds R C).powerset, ∀ Yt b, (∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
        (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
            coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
          ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) ≠ ⊤ := fun bad hbad Yt b => by
    rw [← key bad hbad Yt b]
    exact ENNReal.ofReal_ne_top
  rw [caseIntegral_eq_sum_integral h1]
  unfold coarseStateWeight coarseStateMass
  rw [ENNReal.toReal_sum (fun bad hb => ENNReal.sum_ne_top.mpr fun Yt _ => ENNReal.sum_ne_top.mpr fun b _ =>
    hfin bad hb Yt b)]
  refine Finset.sum_congr rfl fun bad hbad => ?_
  rw [ENNReal.toReal_sum (fun Yt _ => ENNReal.sum_ne_top.mpr fun b _ => hfin bad hbad Yt b)]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [ENNReal.toReal_sum (fun b _ => hfin bad hbad Yt b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← key bad hbad Yt b]
  exact (ENNReal.toReal_ofReal (hI bad Yt b)).symm
private theorem caseMean_one_eq (hG : StepWeightsNonneg R n) (h1 : CaseIntegrable R C V q fun _ _ _ _ _ => 1)
    (hp : coarseStateWeight R C V q ≠ 0) : caseMean R C V q (fun _ _ _ _ _ => 1) = 1 := by
  unfold caseMean
  rw [caseIntegral_one_eq hG h1, div_self hp]
private theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fillLabels <;> assumption
private theorem caseIntegrable_of_abs_le (hG : StepWeightsNonneg R n) {F M : CaseFunction R n}
    (h1 : CaseIntegrable R C V q fun _ _ _ _ _ => 1) (hM : CaseIntegrable R C V q M)
    (hm : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      (open Classical in Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then F p.1 Yt p.2 bad b else 0))
    (hb : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → |F W Yt ωt bad b| ≤ M W Yt ωt bad b) :
    CaseIntegrable R C V q F := fun bad hbad Yt b => by
  classical
  have hφ : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) :=
    ((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk ((measurable_fillLabels q Yt).comp measurable_snd)
  have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q F bad Yt b p.1 p.2) = fun p =>
      (if IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) then
        F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b else 0) *
      caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2 := by
    funext p
    unfold caseTerm
    split_ifs with hc hl
    · ring
    · rw [stepWeight_eq_zero_of_not_live hG C V _ bad b hc.1 hl]
      ring
    · ring
    · ring
  have hae : AEStronglyMeasurable (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q F bad Yt b p.1 p.2)
      ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := by
    rw [e]
    exact ((hm Yt bad b).comp hφ).aestronglyMeasurable.mul (h1 bad hbad Yt b).aestronglyMeasurable
  refine (hM bad hbad Yt b).mono hae (Filter.Eventually.of_forall fun p => ?_)
  have := abs_caseTerm_le (q := q) (C := C) (V := V) hG hb bad Yt b p.1 p.2
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact this.trans (le_abs_self _)
end Calculus
section OneLevel
variable {R : StepSetup} {n : ℕ} [NeZero n] {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
def LiveMeasurable (R : StepSetup) (m : ℕ) [NeZero m] (Yt : Finset (TorusSite m))
    (h : TorusField m × (Yt → R.labels.Ω) → ℝ) : Prop :=
  open Classical in Measurable fun p : TorusField m × (Yt → R.labels.Ω) =>
    if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then h p else 0
private theorem LiveMeasurable.mul {m : ℕ} [NeZero m] {Yt : Finset (TorusSite m)}
    {h h' : TorusField m × (Yt → R.labels.Ω) → ℝ} (a : LiveMeasurable R m Yt h) (a' : LiveMeasurable R m Yt h') :
    LiveMeasurable R m Yt fun p => h p * h' p := by
  classical
  have e : (fun p : TorusField m × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then h p * h' p else 0) = fun p =>
      (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then h p else 0) *
        (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then h' p else 0) := by
    funext p
    split_ifs <;> simp
  unfold LiveMeasurable
  convert Measurable.mul a a' using 1
  exact e
private theorem LiveMeasurable.add {m : ℕ} [NeZero m] {Yt : Finset (TorusSite m)}
    {h h' : TorusField m × (Yt → R.labels.Ω) → ℝ} (a : LiveMeasurable R m Yt h) (a' : LiveMeasurable R m Yt h') :
    LiveMeasurable R m Yt fun p => h p + h' p := by
  classical
  have e : (fun p : TorusField m × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then h p + h' p else 0) = fun p =>
      (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then h p else 0) +
        (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then h' p else 0) := by
    funext p
    split_ifs <;> simp
  unfold LiveMeasurable
  convert Measurable.add a a' using 1
  exact e
private theorem LiveMeasurable.of_measurable {m : ℕ} [NeZero m] {Yt : Finset (TorusSite m)}
    {h : TorusField m × (Yt → R.labels.Ω) → ℝ}
    (hs : open Classical in MeasurableSet {p : TorusField m × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2}) (a : Measurable h) :
    LiveMeasurable R m Yt h := by
  classical
  unfold LiveMeasurable
  exact Measurable.ite hs a measurable_const
private theorem LiveMeasurable.prod {m : ℕ} [NeZero m] {Yt : Finset (TorusSite m)} {κ : Type} (S : Finset κ)
    {h : κ → TorusField m × (Yt → R.labels.Ω) → ℝ}
    (hs : open Classical in MeasurableSet {p : TorusField m × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2})
    (a : ∀ k ∈ S, LiveMeasurable R m Yt (h k)) : LiveMeasurable R m Yt fun p => ∏ k ∈ S, h k p := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using LiveMeasurable.of_measurable hs measurable_const
  | insert k S hk ih =>
    simp only [Finset.prod_insert hk]
    exact (a k (Finset.mem_insert_self _ _)).mul (ih fun j hj => a j (Finset.mem_insert_of_mem hj))
private theorem LiveMeasurable.sum {m : ℕ} [NeZero m] {Yt : Finset (TorusSite m)} {κ : Type} (S : Finset κ)
    {h : κ → TorusField m × (Yt → R.labels.Ω) → ℝ}
    (hs : open Classical in MeasurableSet {p : TorusField m × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2})
    (a : ∀ k ∈ S, LiveMeasurable R m Yt (h k)) : LiveMeasurable R m Yt fun p => ∑ k ∈ S, h k p := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using LiveMeasurable.of_measurable hs measurable_const
  | insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    exact (a k (Finset.mem_insert_self _ _)).add (ih fun j hj => a j (Finset.mem_insert_of_mem hj))
open Classical in
private theorem stageStepMomentBound (hG : StepWeightsNonneg R n) {ι : Type} (I : Finset ι)
    (Fs : ι → (W : TorusField (n * R.params.side)) → (Yt : Finset (TorusSite (n * R.params.side))) →
      (Yt → R.labels.Ω) → ℝ)
    (sl : ι → TorusField (n * R.params.side) → BaseChoice R.params.side n → ℝ)
    (Ns : ι → (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ)
    (Gm : Finset ι → (W : TorusField (n * R.params.side)) → (Yt : Finset (TorusSite (n * R.params.side))) →
      (Yt → R.labels.Ω) → ℝ)
    (Err : Finset ι → ℝ) (κ s2 : ι → ℝ) (Bd : ℝ)
    (hset : ∀ Yt : Finset (TorusSite (n * R.params.side)),
      MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
        IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2})
    (h1 : CaseIntegrable R C V q fun _ _ _ _ _ => 1)
    (hN : ∀ J ⊆ I, CaseIntegrable R C V q fun _ Yt ωt _ _ => ∏ i ∈ J, Ns i Yt ωt)
    (hNle : ∀ J ⊆ I, caseMean R C V q (fun _ Yt ωt _ _ => ∏ i ∈ J, Ns i Yt ωt) ≤ Bd)
    (hNs : ∀ i Yt ωt, 0 ≤ Ns i Yt ωt) (hκ : ∀ i, 0 ≤ κ i) (hs2 : ∀ i, 0 ≤ s2 i)
    (hsl : ∀ i ∈ I, ∀ W b, |sl i W b| ≤ s2 i)
    (hF : ∀ i ∈ I, ∀ W Yt ωt, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |Fs i W Yt ωt| ≤ κ i * Ns i Yt ωt)
    (hFm : ∀ i Yt, LiveMeasurable R (n * R.params.side) Yt fun p => Fs i p.1 Yt p.2)
    (hGm : ∀ J ⊆ I, ∀ Yt, LiveMeasurable R (n * R.params.side) Yt fun p => Gm J p.1 Yt p.2)
    (hsm : ∀ i b, Measurable fun W : TorusField (n * R.params.side) => sl i W b)
    (hIH : ∀ J ⊆ I, ∀ W Yt ωt, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |Gm J W Yt ωt - ∏ i ∈ J, Fs i W Yt ωt| ≤ Err J * ∏ i ∈ J, Ns i Yt ωt)
    (hErr : ∀ J ⊆ I, 0 ≤ Err J) :
    |∑ J ∈ I.powerset, caseMean R C V q (fun W Yt ωt _ b => Gm J W Yt ωt * ∏ i ∈ I \ J, sl i W b) -
        caseMean R C V q (fun W Yt ωt _ b => ∏ i ∈ I, (Fs i W Yt ωt + sl i W b))| ≤
      (∑ J ∈ I.powerset, Err J * ∏ i ∈ I \ J, s2 i) * Bd := by
  set As : Finset ι → CaseFunction R n := fun J W Yt ωt _ b => Gm J W Yt ωt * ∏ i ∈ I \ J, sl i W b with hAs
  set Bs : Finset ι → CaseFunction R n := fun J W Yt ωt _ b => (∏ i ∈ J, Fs i W Yt ωt) * ∏ i ∈ I \ J, sl i W b
    with hBs
  have hslb : ∀ J : Finset ι, ∀ W b, |∏ i ∈ I \ J, sl i W b| ≤ ∏ i ∈ I \ J, s2 i := fun J W b => by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi => hsl i (Finset.mem_sdiff.mp hi).1 W b
  have hs2p : ∀ J : Finset ι, 0 ≤ ∏ i ∈ I \ J, s2 i := fun J => Finset.prod_nonneg fun i _ => hs2 i
  have hNp : ∀ (J : Finset ι) Yt ωt, 0 ≤ ∏ i ∈ J, Ns i Yt ωt := fun J Yt ωt =>
    Finset.prod_nonneg fun i _ => hNs i Yt ωt
  have hκp : ∀ J : Finset ι, 0 ≤ ∏ i ∈ J, κ i := fun J => Finset.prod_nonneg fun i _ => hκ i
  have hFb : ∀ J ⊆ I, ∀ W Yt ωt, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |∏ i ∈ J, Fs i W Yt ωt| ≤ (∏ i ∈ J, κ i) * ∏ i ∈ J, Ns i Yt ωt := fun J hJ W Yt ωt hl => by
    rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi => hF i (hJ hi) W Yt ωt hl
  have hslm : ∀ (J : Finset ι) Yt b, LiveMeasurable R (n * R.params.side) Yt fun p => ∏ i ∈ I \ J, sl i p.1 b :=
    fun J Yt b =>
    LiveMeasurable.prod _ (hset Yt) fun i _ => LiveMeasurable.of_measurable (hset Yt) ((hsm i b).comp measurable_fst)
  have hBs_int : ∀ J ⊆ I, CaseIntegrable R C V q (Bs J) := fun J hJ => by
    refine caseIntegrable_of_abs_le hG h1 (caseIntegrable_const_mul ((∏ i ∈ J, κ i) * ∏ i ∈ I \ J, s2 i) (hN J hJ))
      ?_ ?_
    · intro Yt bad b
      exact (LiveMeasurable.prod J (hset Yt) fun i _ => hFm i Yt).mul (hslm J Yt b)
    · intro W Yt ωt bad b hl
      simp only [hBs]
      rw [abs_mul]
      calc |∏ i ∈ J, Fs i W Yt ωt| * |∏ i ∈ I \ J, sl i W b|
          ≤ ((∏ i ∈ J, κ i) * ∏ i ∈ J, Ns i Yt ωt) * ∏ i ∈ I \ J, s2 i :=
            mul_le_mul (hFb J hJ W Yt ωt hl) (hslb J W b) (abs_nonneg _) (mul_nonneg (hκp J) (hNp J Yt ωt))
        _ = _ := by ring
  have hAs_int : ∀ J ⊆ I, CaseIntegrable R C V q (As J) := fun J hJ => by
    refine caseIntegrable_of_abs_le hG h1
      (caseIntegrable_const_mul ((Err J + ∏ i ∈ J, κ i) * ∏ i ∈ I \ J, s2 i) (hN J hJ)) ?_ ?_
    · intro Yt bad b
      exact (hGm J hJ Yt).mul (hslm J Yt b)
    · intro W Yt ωt bad b hl
      simp only [hAs]
      rw [abs_mul]
      have hg : |Gm J W Yt ωt| ≤ (Err J + ∏ i ∈ J, κ i) * ∏ i ∈ J, Ns i Yt ωt := by
        have h₁ := hIH J hJ W Yt ωt hl
        have h₂ := hFb J hJ W Yt ωt hl
        have h₃ := abs_sub_abs_le_abs_sub (Gm J W Yt ωt) (∏ i ∈ J, Fs i W Yt ωt)
        linarith
      calc |Gm J W Yt ωt| * |∏ i ∈ I \ J, sl i W b|
          ≤ ((Err J + ∏ i ∈ J, κ i) * ∏ i ∈ J, Ns i Yt ωt) * ∏ i ∈ I \ J, s2 i :=
            mul_le_mul hg (hslb J W b) (abs_nonneg _)
              (mul_nonneg (add_nonneg (hErr J hJ) (hκp J)) (hNp J Yt ωt))
        _ = _ := by ring
  have hsum : caseMean R C V q (fun W Yt ωt _ b => ∏ i ∈ I, (Fs i W Yt ωt + sl i W b)) =
      ∑ J ∈ I.powerset, caseMean R C V q (Bs J) := by
    rw [← caseMean_sum_fn I.powerset fun J hJ => hBs_int J (Finset.mem_powerset.mp hJ)]
    congr 1
    funext W Yt ωt bad b
    rw [Finset.prod_add]
  rw [hsum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun J hJ' => ?_)
  have hJ := Finset.mem_powerset.mp hJ'
  rw [← caseMean_sub_fn (hAs_int J hJ) (hBs_int J hJ)]
  have hM := caseIntegrable_const_mul (Err J * ∏ i ∈ I \ J, s2 i) (hN J hJ)
  refine (abs_caseMean_le hG (caseIntegrable_sub (hAs_int J hJ) (hBs_int J hJ)) hM ?_).trans ?_
  · intro W Yt ωt bad b hl
    simp only [hAs, hBs]
    rw [← sub_mul, abs_mul]
    calc |Gm J W Yt ωt - ∏ i ∈ J, Fs i W Yt ωt| * |∏ i ∈ I \ J, sl i W b|
        ≤ (Err J * ∏ i ∈ J, Ns i Yt ωt) * ∏ i ∈ I \ J, s2 i :=
          mul_le_mul (hIH J hJ W Yt ωt hl) (hslb J W b) (abs_nonneg _)
            (mul_nonneg (hErr J hJ) (hNp J Yt ωt))
      _ = _ := by ring
  · rw [caseMean_const_mul_fn _ (hN J hJ)]
    exact mul_le_mul_of_nonneg_left (hNle J hJ) (mul_nonneg (hErr J hJ) (hs2p J))
end OneLevel
section Sites
variable {L : ℕ} [NeZero L]
private theorem isPlaquetteAt_succ {t n : ℕ} [NeZero n] (Y : TorusSite n) (p : TorusPlaquette (fineSide L (t + 1) n)) :
    IsPlaquetteAt L (t + 1) Y p ↔ ∃ y : TorusSite (n * L), parentBlock L y = Y ∧ IsPlaquetteAt L t y p := by
  classical
  have key : ∀ c : TorusSite (fineSide L t (n * L)), c ∈ fineBlock L (t + 1) n Y ↔
      ∃ y : TorusSite (n * L), parentBlock L y = Y ∧ c ∈ fineBlock L t (n * L) y := by
    intro c
    show c ∈ (sitesInBlocks L {Y}).biUnion (fun y => fineBlock L t (n * L) y) ↔ _
    simp only [sitesInBlocks, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  unfold IsPlaquetteAt
  constructor
  · rintro ⟨h, c, hc, hcb⟩
    obtain ⟨y, hy, hcy⟩ := (key c).mp hcb
    exact ⟨y, hy, h, c, hc, hcy⟩
  · rintro ⟨y, hy, h, c, hc, hcy⟩
    exact ⟨h, c, hc, (key c).mpr ⟨y, hy, hcy⟩⟩
open Classical in
private theorem image_weightSupportSites {t n : ℕ} [NeZero n] (f : PlaquetteWeight (fineSide L (t + 1) n)) :
    (weightSupportSites L t (n * L) f).image (parentBlock L) = weightSupportSites L (t + 1) n f := by
  ext Y
  simp only [weightSupportSites, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, isPlaquetteAt_succ]
  constructor
  · rintro ⟨y, ⟨p, hp, hf⟩, rfl⟩
    exact ⟨p, ⟨y, rfl, hp⟩, hf⟩
  · rintro ⟨p, ⟨y, rfl, hp⟩, hf⟩
    exact ⟨y, ⟨p, hp, hf⟩, rfl⟩
abbrev _root_.YangMills.SharedProofs.p19152 := @image_weightSupportSites
private theorem weightLipschitz_mono (hL : 1 ≤ L) (t : ℕ) {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    weightLipschitz L t h ≤ weightLipschitz L (t + 1) h := by
  unfold weightLipschitz
  refine ciSup_mono (Set.finite_range _).bddAbove fun pp => ?_
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  unfold barycentreDist
  set d : ℝ := (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  rcases hd.eq_or_lt with h0 | hpos
  · simp [← h0]
  · have hp : (0 : ℝ) < (L : ℝ) ^ t := pow_pos (by linarith) t
    refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
    refine div_le_div_of_nonneg_left hd (by positivity) ?_
    rw [pow_succ]
    nlinarith
abbrev _root_.YangMills.SharedProofs.p58015 := @weightLipschitz_mono
private theorem weightNorm_mono (hL : 1 ≤ L) (t : ℕ) {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    weightNorm L t h ≤ weightNorm L (t + 1) h :=
  max_le_max le_rfl (weightLipschitz_mono hL t h)
end Sites
section Facts
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
private theorem one_le_meanSiteScore {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (B Y : Finset (TorusSite n))
    (ω : Y → Ω) : 1 ≤ meanSiteScore s B Y ω := by
  unfold meanSiteScore
  have : 0 ≤ ∑ y ∈ B, siteScore s Y ω y := Finset.sum_nonneg fun y _ => by
    unfold siteScore
    split_ifs
    · exact hs _
    · exact le_rfl
  have h2 : 0 ≤ (B.card : ℝ)⁻¹ := by positivity
  nlinarith [mul_nonneg h2 this]
abbrev _root_.YangMills.SharedProofs.p16546 := @one_le_meanSiteScore
private theorem meanSiteScore_empty {Ω : Type} (s : Ω → ℝ) (Y : Finset (TorusSite n)) (ω : Y → Ω) :
    meanSiteScore s ∅ Y ω = 1 := by
  simp [meanSiteScore]
private theorem abs_blockBondScores_le (hS : BondScoreProperties) (hf : R.params.Admissible)
    (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n) (Y : TorusSite n) :
    |blockBondScores (R := R) W V b Y| ≤ 16 := by
  unfold blockBondScores
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ c : TorusBond n, |bondScore R.params R.coupling W V b c| ≤ 2 := fun c =>
    (hS R.params hf R.coupling n b c).2.2.1 W V
  have : ∀ i : Fin 4, |bondScore R.params R.coupling W V b (Y, i) +
      bondScore R.params R.coupling W V b (Y - TorusFields.unitStep n i, i)| ≤ 4 := fun i =>
    (abs_add_le _ _).trans (by linarith [h (Y, i), h (Y - TorusFields.unitStep n i, i)])
  calc _ ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = 16 := by norm_num
abbrev _root_.YangMills.SharedProofs.p16371 := @abs_blockBondScores_le
private theorem measurable_blockBondScores (hS : BondScoreProperties) (hf : R.params.Admissible) (V : TorusField n)
    (b : BaseChoice R.params.side n) (Y : TorusSite n) :
    Measurable fun W : TorusField (n * R.params.side) => blockBondScores (R := R) W V b Y := by
  unfold blockBondScores
  have hp : Measurable fun W : TorusField (n * R.params.side) => (W, V) := measurable_id.prodMk measurable_const
  have h : ∀ c : TorusBond n, Measurable fun W : TorusField (n * R.params.side) =>
      bondScore R.params R.coupling W V b c := fun c => by
    have h0 := (hS R.params hf R.coupling n b c).2.2.2.2
    exact Measurable.comp (g := fun p : TorusField (n * R.params.side) × TorusField n =>
        bondScore R.params R.coupling p.1 p.2 b c)
      (f := fun W : TorusField (n * R.params.side) => (W, V)) h0 hp
  have h1 : ∀ i : Fin 4, Measurable fun W : TorusField (n * R.params.side) =>
      bondScore R.params R.coupling W V b (Y, i) + bondScore R.params R.coupling W V b (Y - TorusFields.unitStep n i, i) :=
    fun i => (h (Y, i)).add (h (Y - TorusFields.unitStep n i, i))
  exact Finset.measurable_sum Finset.univ fun i _ => h1 i
abbrev _root_.YangMills.SharedProofs.p16256 := @measurable_blockBondScores
private def weightedScoreTerm (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) : ℝ :=
  R.params.coupling / 2 * A.coeff * (∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
    blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y)
private theorem abs_weightedScoreTerm_le (hS : BondScoreProperties) (hW : WeightsCloseToBlockMeans)
    (hf : R.params.Admissible) (hal : |A.coeff| ≤ 2) (V : TorusField n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (hs : weightNorm R.params.side (R.depth + 1) f ≤ 1)
    (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    |weightedScoreTerm A V f W b| ≤
      16 * R.params.coupling * ((weightSupportSites R.params.side (R.depth + 1) n f).card : ℝ) := by
  unfold weightedScoreTerm
  have ha : 0 < R.params.coupling := by linarith [hf.a_ge]
  have hterm : ∀ Y, |blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y| ≤ 16 := fun Y => by
    rw [abs_mul]
    have h1 : |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1 :=
      ((hW R.params.side hf.L_odd (R.depth + 1) n Y).1 f).trans ((le_max_left _ _).trans hs)
    have h2 := abs_blockBondScores_le hS hf W V b Y
    calc _ ≤ 1 * 16 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 16 := by norm_num
  have hsum : |∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
      blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y| ≤
      16 * ((weightSupportSites R.params.side (R.depth + 1) n f).card : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, (16 : ℝ) :=
          Finset.sum_le_sum fun Y _ => hterm Y
      _ = _ := by simp [mul_comm]
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < R.params.coupling / 2)]
  calc R.params.coupling / 2 * |A.coeff| * _ ≤ R.params.coupling / 2 * 2 *
        (16 * ((weightSupportSites R.params.side (R.depth + 1) n f).card : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hal (by positivity)) hsum (abs_nonneg _) (by positivity)
    _ = _ := by ring
private theorem measurable_weightedScoreTerm (hS : BondScoreProperties) (hf : R.params.Admissible) (V : TorusField n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) => weightedScoreTerm A V f W b := by
  unfold weightedScoreTerm
  exact (Finset.measurable_sum _ fun Y _ => (measurable_blockBondScores hS hf V b Y).const_mul _).const_mul _
private theorem abs_supportResponseTotal_le (hI : A.IsAdmissible) (hC : 1 ≤ A.responseParams.C₀) {m : ℕ} [NeZero m]
    (hb : IsBlockTorusSide R.params m) (f : PlaquetteWeight (fineSide R.params.side R.depth m))
    (hs : weightNorm R.params.side R.depth f ≤ 1) (W : TorusField m) (Y : Finset (TorusSite m)) (ω : Y → R.labels.Ω)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Y ω) :
    |supportResponseTotal A f W Y ω| ≤ A.responseParams.C₀ *
      ((weightSupportSites R.params.side R.depth m f).card : ℝ) *
      meanSiteScore A.score (weightSupportSites R.params.side R.depth m f) Y ω := by
  have hnn : ∀ y, 0 ≤ siteScore A.score Y ω y := fun y => by
    unfold siteScore
    split_ifs
    · exact hI.price.nonneg _
    · exact le_rfl
  set S := weightSupportSites R.params.side R.depth m f with hS
  have hterm : ∀ y ∈ S, |centeredHullResponse A.cold A.hull m y W Y ω f| ≤
      A.responseParams.C₀ + siteScore A.score Y ω y := fun y _ => by
    have h := hI.bounds.size_hull m hb y W Y ω hl f
    have h0 : 0 ≤ A.responseParams.C₀ + siteScore A.score Y ω y := by linarith [hnn y]
    exact h.trans (by nlinarith)
  have h1 : |supportResponseTotal A f W Y ω| ≤ A.responseParams.C₀ * (S.card : ℝ) + ∑ y ∈ S, siteScore A.score Y ω y := by
    unfold supportResponseTotal
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_add_distrib]
    simp [mul_comm]
  have hsum : 0 ≤ ∑ y ∈ S, siteScore A.score Y ω y := Finset.sum_nonneg fun y _ => hnn y
  rcases S.eq_empty_or_nonempty with he | hne
  · have : ∑ y ∈ S, siteScore A.score Y ω y = 0 := by simp [he]
    rw [this] at h1
    simpa [he, meanSiteScore] using h1
  · have hc : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
    unfold meanSiteScore
    have e : A.responseParams.C₀ * (S.card : ℝ) * (1 + (S.card : ℝ)⁻¹ * ∑ y ∈ S, siteScore A.score Y ω y) =
        A.responseParams.C₀ * (S.card : ℝ) + A.responseParams.C₀ * ∑ y ∈ S, siteScore A.score Y ω y := by
      field_simp
    rw [e]
    nlinarith
abbrev _root_.YangMills.SharedProofs.p79992 := @abs_supportResponseTotal_le
private theorem hull_eq_zero_off_support (hI : A.IsAdmissible) {m : ℕ} [NeZero m] (hb : IsBlockTorusSide R.params m)
    (y : TorusSite m) (f : PlaquetteWeight (fineSide R.params.side R.depth m))
    (hy : ∀ p, IsPlaquetteAt R.params.side R.depth y p → f p = 0) (W : TorusField m) (Y : Finset (TorusSite m))
    (ω : Y → R.labels.Ω) (hl : IsLiveState R.params R.coupling R.labelWeight W Y ω) : A.hull m y W Y ω f = 0 := by
  have h1 := hI.bounds.hull_reads m hb y W Y ω hl f 0 (fun p hp => by simpa using hy p hp)
  have h2 := hI.bounds.hull_linear m hb y W Y ω hl 1 0 0
  simp only [one_smul, add_zero, one_mul] at h2
  rw [h1]
  linarith
end Facts
section Ground
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
def MeanScoreMajorant (ch : ℝ) (R : StepSetup) (A : ResponseSetup R) (n : ℕ) [NeZero n] : Prop :=
  ∀ G : GasGround R n, G.IsAdmissibleGround →
    ∀ (ι : Type) (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side))), (∀ i ∈ I, (B i).Nonempty) →
      CaseIntegrable R G.cut G.coarse G.state (fun _ Yt ωt _ _ => ∏ i ∈ I, meanSiteScore A.score (B i) Yt ωt) ∧
      caseMean R G.cut G.coarse G.state (fun _ Yt ωt _ _ => ∏ i ∈ I, meanSiteScore A.score (B i) Yt ωt) ≤
        Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * ch * R.coupling))) *
          ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
            (open Classical in (B i).image (parentBlock R.params.side)) G.state.1 G.state.2
variable {A}
private theorem integrable_one {ch : ℝ} (hM : MeanScoreMajorant ch R A n) {G : GasGround R n}
    (hg : G.IsAdmissibleGround) : CaseIntegrable R G.cut G.coarse G.state fun _ _ _ _ _ => 1 := by
  simpa using (hM G hg Unit ∅ (fun _ => ∅) (by simp)).1
private theorem integrable_meanSiteScore {ch : ℝ} (hM : MeanScoreMajorant ch R A n) {G : GasGround R n}
    (hg : G.IsAdmissibleGround) {B : Finset (TorusSite (n * R.params.side))} (hB : B.Nonempty) :
    CaseIntegrable R G.cut G.coarse G.state fun _ Yt ωt _ _ => meanSiteScore A.score B Yt ωt := by
  simpa using (hM G hg Unit {()} (fun _ => B) (by simpa using hB)).1
private theorem measurableSet_live (hr : R.HasExpansions) {m : ℕ} [NeZero m] (hb : IsBlockTorusSide R.params m)
    (Yt : Finset (TorusSite m)) :
    MeasurableSet {p : TorusField m × (Yt → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have h := (hr.2.borel m hb Yt).1
  have e : {p : TorusField m × (Yt → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} =
      (fun p : TorusField m × (Yt → R.labels.Ω) =>
        if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight m p.1 Yt p.2 else 0) ⁻¹'
        Set.Ioi 0 := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, IsLiveState]
    split_ifs with hh
    · simp [hh]
    · simp [hh]
  rw [e]
  convert h measurableSet_Ioi using 3
abbrev _root_.YangMills.SharedProofs.p107331 := @measurableSet_live
private theorem liveMeasurable_hull (hI : A.IsAdmissible) {m : ℕ} [NeZero m] (hb : IsBlockTorusSide R.params m)
    (y : TorusSite m) (Yt : Finset (TorusSite m)) (h : PlaquetteWeight (fineSide R.params.side R.depth m)) :
    LiveMeasurable R m Yt fun p => A.hull m y p.1 Yt p.2 h := by
  unfold LiveMeasurable
  convert hI.bounds.hull_borel m hb y Yt h using 3
private theorem liveMeasurable_supportResponseTotal (hr : R.HasExpansions) (hI : A.IsAdmissible) {m : ℕ} [NeZero m]
    (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m))
    (h : PlaquetteWeight (fineSide R.params.side R.depth m)) :
    LiveMeasurable R m Yt fun p => supportResponseTotal A h p.1 Yt p.2 := by
  have hs := measurableSet_live hr hb Yt
  unfold supportResponseTotal
  refine LiveMeasurable.sum _ hs fun y _ => ?_
  unfold centeredHullResponse
  have := (liveMeasurable_hull hI hb y Yt h).add
    (LiveMeasurable.of_measurable hs (measurable_const (a := - A.cold m y (trivialField m) h)))
  simpa [sub_eq_add_neg] using this
private theorem integrable_hull (hr : R.HasExpansions) {ch : ℝ} (hM : MeanScoreMajorant ch R A n) (hI : A.IsAdmissible)
    (hC : 1 ≤ A.responseParams.C₀) (hb : IsBlockTorusSide R.params (n * R.params.side)) {G : GasGround R n}
    (hg : G.IsAdmissibleGround) (hG : StepWeightsNonneg R n) (y : TorusSite (n * R.params.side))
    (f : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
    (hs : weightNorm R.params.side R.depth f ≤ 1) :
    CaseIntegrable R G.cut G.coarse G.state fun W Yt ωt _ _ => A.hull (n * R.params.side) y W Yt ωt f := by
  refine caseIntegrable_of_abs_le hG (integrable_one hM hg)
    (caseIntegrable_const_mul (A.responseParams.C₀ + |A.cold (n * R.params.side) y (trivialField _) f|)
      (integrable_meanSiteScore hM hg (Finset.singleton_nonempty y))) ?_ ?_
  · intro Yt bad b
    exact liveMeasurable_hull hI hb y Yt f
  · intro W Yt ωt bad b hl
    have h := hI.bounds.size_hull (n * R.params.side) hb y W Yt ωt hl f
    have hnn : 0 ≤ siteScore A.score Yt ωt y := by
      unfold siteScore
      split_ifs
      · exact hI.price.nonneg _
      · exact le_rfl
    have h' : |centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f| ≤
        A.responseParams.C₀ + siteScore A.score Yt ωt y :=
      h.trans (by nlinarith)
    have e : A.hull (n * R.params.side) y W Yt ωt f =
        centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f +
          A.cold (n * R.params.side) y (trivialField _) f := by
      unfold centeredHullResponse
      ring
    have hms : meanSiteScore A.score {y} Yt ωt = 1 + siteScore A.score Yt ωt y := by
      simp [meanSiteScore]
    rw [e, hms]
    have h2 := abs_add_le (centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
      (A.cold (n * R.params.side) y (trivialField _) f)
    have h3 := abs_nonneg (A.cold (n * R.params.side) y (trivialField _) f)
    nlinarith
private theorem integrable_blockBondScores (hS : BondScoreProperties) (hr : R.HasExpansions) (hf : R.params.Admissible)
    {ch : ℝ} (hM : MeanScoreMajorant ch R A n) (hb : IsBlockTorusSide R.params (n * R.params.side)) {G : GasGround R n}
    (hg : G.IsAdmissibleGround) (hG : StepWeightsNonneg R n) (c : ℝ) (Y : TorusSite n) :
    CaseIntegrable R G.cut G.coarse G.state fun W _ _ _ b => c * blockBondScores W G.coarse b Y := by
  refine caseIntegrable_of_abs_le hG (integrable_one hM hg) (caseIntegrable_const_mul (|c| * 16) (integrable_one hM hg))
    ?_ ?_
  · intro Yt bad b
    exact LiveMeasurable.of_measurable (measurableSet_live hr hb Yt)
      (((measurable_blockBondScores hS hf G.coarse b Y).comp measurable_fst).const_mul c)
  · intro W Yt ωt bad b hl
    rw [abs_mul, mul_one]
    exact mul_le_mul_of_nonneg_left (abs_blockBondScores_le hS hf W G.coarse b Y) (abs_nonneg _)
private theorem integrable_caseResponse (hS : BondScoreProperties) (hr : R.HasExpansions) (hf : R.params.Admissible)
    {ch : ℝ} (hM : MeanScoreMajorant ch R A n) (hI : A.IsAdmissible) (hC : 1 ≤ A.responseParams.C₀)
    (hb : IsBlockTorusSide R.params (n * R.params.side)) {G : GasGround R n} (hg : G.IsAdmissibleGround)
    (hG : StepWeightsNonneg R n) (Y : TorusSite n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hs : weightNorm R.params.side R.depth f ≤ 1) :
    CaseIntegrable R G.cut G.coarse G.state (caseResponse A G.coarse Y f) := by
  unfold caseResponse
  exact caseIntegrable_add (caseIntegrable_sum _ (fun y _ => integrable_hull hr hM hI hC hb hg hG y f hs)
    caseIntegrable_zero) (integrable_blockBondScores hS hr hf hM hb hg hG _ Y)
open Classical in
private theorem supportResponseSum_eq (hI : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    supportResponseSum A V f W Yt ωt bad b =
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, caseResponse A V Y f W Yt ωt bad b -
        ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          A.cold (n * R.params.side) y (trivialField _) f := by
  set S := weightSupportSites R.params.side R.depth (n * R.params.side) f with hSdef
  set S' := weightSupportSites R.params.side (R.depth + 1) n f with hS'def
  have hmaps : ∀ y ∈ S, parentBlock R.params.side y ∈ S' := fun y hy => by
    rw [hS'def, ← image_weightSupportSites]
    exact Finset.mem_image_of_mem _ hy
  have hQ : ∑ Y ∈ S', ∑ y ∈ sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) y W Yt ωt f =
      ∑ y ∈ S, A.hull (n * R.params.side) y W Yt ωt f := by
    have h1 : ∑ y ∈ S, A.hull (n * R.params.side) y W Yt ωt f =
        ∑ y ∈ Finset.univ.filter (fun y => parentBlock R.params.side y ∈ S'), A.hull (n * R.params.side) y W Yt ωt f := by
      refine Finset.sum_subset (fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmaps y hy⟩) fun y _ hy => ?_
      refine hull_eq_zero_off_support A hI hb y f (fun p hp => ?_) W Yt ωt hl
      by_contra hne
      exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, hne⟩)
    rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun y => parentBlock R.params.side y ∈ S'))
      (t := S') (g := parentBlock R.params.side) (fun y hy => (Finset.mem_filter.mp hy).2)]
    refine Finset.sum_congr rfl fun Y hY => Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact ⟨h ▸ hY, h⟩
    · exact fun h => h.2
  unfold supportResponseSum caseResponse centeredHullResponse
  rw [Finset.sum_add_distrib, hQ, Finset.sum_sub_distrib, Finset.mul_sum]
  have : ∑ Y ∈ S', R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y f *
      blockBondScores W V b Y =
      ∑ Y ∈ S', R.params.coupling / 2 * A.coeff *
        (blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  change (∑ y ∈ S, A.hull (n * R.params.side) y W Yt ωt f - ∑ y ∈ S, A.cold (n * R.params.side) y (trivialField _) f) +
    ∑ Y ∈ S', R.params.coupling / 2 * A.coeff *
      (blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y) = _
  ring
abbrev _root_.YangMills.SharedProofs.p27295 := @supportResponseSum_eq
end Ground
section Means
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n] {ch : ℝ}
structure StepHypotheses (ch : ℝ) (R : StepSetup) (A : ResponseSetup R) (n : ℕ) [NeZero n] : Prop where
  weights_nonneg : StepWeightsNonneg R n
  expansions : R.HasExpansions
  admissible : R.params.Admissible
  response : A.IsAdmissible
  block_side : IsBlockTorusSide R.params (n * R.params.side)
  majorant : MeanScoreMajorant ch R A n
  bondScores : BondScoreProperties
  blockMeans : WeightsCloseToBlockMeans
  cold_ground : (coldCaseGround R (trivialField n)).IsAdmissibleGround
  cold_mass_ne_zero : coarseStateWeight R ∅ (trivialField n) (emptyCoarseState R) ≠ 0
  exp_small : Real.exp (2 * Real.exp (-(7 * ch * R.coupling))) ≤ 11 / 10
private theorem C₀_ge_of_admissible (hI : A.IsAdmissible) : 14 + 40 * R.params.coupling ≤ A.responseParams.C₀ := by
  have hk := hI.params_admissible
  rw [hk.C₀_eq]
  linarith [hk.N₀_nonneg, hk.Kc_ge]
private theorem C₀_ge (hs : StepHypotheses ch R A n) : 14 + 40 * R.params.coupling ≤ A.responseParams.C₀ :=
  C₀_ge_of_admissible hs.response
private theorem one_le_C₀_of_admissible (hI : A.IsAdmissible) (hf : R.params.Admissible) :
    1 ≤ A.responseParams.C₀ := by
  have h := C₀_ge_of_admissible hI
  have ha := hf.a_ge
  linarith
private theorem one_le_C₀ (hs : StepHypotheses ch R A n) : 1 ≤ A.responseParams.C₀ :=
  one_le_C₀_of_admissible hs.response hs.admissible
private theorem coarseLabelScore_nonneg_of (hI : A.IsAdmissible) (hf : R.params.Admissible)
    (w : CoarseLabel R.labels.Ω R.params.side) : 0 ≤ coarseLabelScore A.responseParams.s₁ A.score w := by
  have hk := hI.params_admissible
  have hC := one_le_C₀_of_admissible hI hf
  have ha := hf.a_ge
  have h1 : 0 ≤ A.responseParams.s₁ := by
    rw [hk.s₁_eq]
    have : 0 ≤ 2 * (R.params.side : ℝ) ^ 4 * (A.responseParams.C₀ + 2) := by positivity
    linarith
  cases w with
  | inl u => exact h1
  | inr st =>
    refine add_nonneg h1 (Finset.sum_nonneg fun o _ => ?_)
    cases st.siteLabel o with
    | inl u => simp
    | inr u => exact hI.price.nonneg u
private theorem coarseLabelScore_nonneg (hs : StepHypotheses ch R A n) (w : CoarseLabel R.labels.Ω R.params.side) :
    0 ≤ coarseLabelScore A.responseParams.s₁ A.score w := coarseLabelScore_nonneg_of hs.response hs.admissible w
private theorem integrable_supportResponseSum (hs : StepHypotheses ch R A n) {G : GasGround R n}
    (hg : G.IsAdmissibleGround) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hz : weightNorm R.params.side R.depth f ≤ 1) :
    CaseIntegrable R G.cut G.coarse G.state (supportResponseSum A G.coarse f) := by
  classical
  have h1 := integrable_one hs.majorant hg
  have h2 := caseIntegrable_sub (caseIntegrable_sum (weightSupportSites R.params.side (R.depth + 1) n f)
    (fun Y _ => integrable_caseResponse hs.bondScores hs.expansions hs.admissible hs.majorant hs.response
      (one_le_C₀ hs) hs.block_side hg hs.weights_nonneg Y f hz) caseIntegrable_zero)
    (caseIntegrable_const_mul (∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
      A.cold (n * R.params.side) y (trivialField _) f) h1)
  refine caseIntegrable_congr_live hs.weights_nonneg (fun W Yt ωt bad b hl => ?_) h2
  rw [supportResponseSum_eq hs.response hs.block_side G.coarse f W Yt ωt bad b hl]
  simp
private theorem caseMean_supportResponseSum (hs : StepHypotheses ch R A n) {G : GasGround R n}
    (hg : G.IsAdmissibleGround) (hp : coarseStateWeight R G.cut G.coarse G.state ≠ 0)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (hz : weightNorm R.params.side R.depth f ≤ 1) :
    caseMean R G.cut G.coarse G.state (supportResponseSum A G.coarse f) =
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
        caseMean R G.cut G.coarse G.state (caseResponse A G.coarse Y f) -
        ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          A.cold (n * R.params.side) y (trivialField _) f := by
  classical
  have h1 := integrable_one hs.majorant hg
  have hc : ∀ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
      CaseIntegrable R G.cut G.coarse G.state (caseResponse A G.coarse Y f) := fun Y _ =>
    integrable_caseResponse hs.bondScores hs.expansions hs.admissible hs.majorant hs.response (one_le_C₀ hs)
      hs.block_side hg hs.weights_nonneg Y f hz
  have e : caseMean R G.cut G.coarse G.state (supportResponseSum A G.coarse f) =
      caseMean R G.cut G.coarse G.state (fun a c d e g =>
        (∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, caseResponse A G.coarse Y f a c d e g) -
        (∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          A.cold (n * R.params.side) y (trivialField _) f) * 1) :=
    caseMean_congr_live hs.weights_nonneg fun W Yt ωt bad b hl => by
      rw [supportResponseSum_eq hs.response hs.block_side G.coarse f W Yt ωt bad b hl, mul_one]
  rw [e, caseMean_sub_fn (caseIntegrable_sum _ hc caseIntegrable_zero) (caseIntegrable_const_mul _ h1),
    caseMean_sum_fn _ hc, caseMean_const_mul_fn _ h1, caseMean_one_eq hs.weights_nonneg h1 hp, mul_one]
private theorem caseMean_centeredSupportResponse (hs : StepHypotheses ch R A n) {G : GasGround R n}
    (hg : G.IsAdmissibleGround) (hp : coarseStateWeight R G.cut G.coarse G.state ≠ 0)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (hz : weightNorm R.params.side R.depth f ≤ 1) :
    caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse f) =
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
        (caseMean R G.cut G.coarse G.state (caseResponse A G.coarse Y f) -
        caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) Y f)) := by
  have h1 := integrable_one hs.majorant hg
  have hv := caseMean_supportResponseSum hs hs.cold_ground hs.cold_mass_ne_zero f hz
  have hv' : caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) =
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
        caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) Y f) -
        ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          A.cold (n * R.params.side) y (trivialField _) f := hv
  have e : caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse f) =
      caseMean R G.cut G.coarse G.state (fun a c d e g => supportResponseSum A G.coarse f a c d e g -
        caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) * 1) := by
    unfold centeredSupportResponse
    simp only [mul_one]
  rw [e, caseMean_sub_fn (integrable_supportResponseSum hs hg f hz) (caseIntegrable_const_mul _ h1),
    caseMean_const_mul_fn _ h1, caseMean_one_eq hs.weights_nonneg h1 hp, mul_one,
    caseMean_supportResponseSum hs hg hp f hz, hv', Finset.sum_sub_distrib]
  ring
private theorem abs_supportResponseSum_le (hs : StepHypotheses ch R A n) (V : TorusField n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hz1 : weightNorm R.params.side (R.depth + 1) f ≤ 1) (hz : weightNorm R.params.side R.depth f ≤ 1)
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    |supportResponseSum A V f W Yt ωt bad b| ≤
      A.responseParams.C₀ * ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ) *
        meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) f) Yt ωt +
        16 * R.params.coupling * ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ) := by
  classical
  have h1 := abs_supportResponseTotal_le A hs.response (one_le_C₀ hs) hs.block_side f hz W Yt ωt hl
  have h2 := abs_weightedScoreTerm_le A hs.bondScores hs.blockMeans hs.admissible hs.response.abs_coeff_le V f hz1 W b
  have hc : ((weightSupportSites R.params.side (R.depth + 1) n f).card : ℝ) ≤
      ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ) := by
    rw [← image_weightSupportSites]
    exact_mod_cast Finset.card_image_le
  have ha : 0 ≤ R.params.coupling := by linarith [hs.admissible.a_ge]
  have e : supportResponseSum A V f W Yt ωt bad b = supportResponseTotal A f W Yt ωt + weightedScoreTerm A V f W b := rfl
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add h1 (h2.trans ?_))
  exact mul_le_mul_of_nonneg_left hc (by positivity)
private theorem abs_stepMeanShift_le (hs : StepHypotheses ch R A n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hz1 : weightNorm R.params.side (R.depth + 1) f ≤ 1) (hz : weightNorm R.params.side R.depth f ≤ 1) :
    |stepMeanShift A f| ≤ (11 / 10 * A.responseParams.C₀ + 16 * R.params.coupling) *
      ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ) := by
  classical
  have hcold := hs.cold_ground
  have h1 := integrable_one hs.majorant hcold
  set S := weightSupportSites R.params.side R.depth (n * R.params.side) f with hS
  rcases S.eq_empty_or_nonempty with he | hne
  · have hS' : weightSupportSites R.params.side (R.depth + 1) n f = ∅ := by
      rw [← image_weightSupportSites, ← hS, he, Finset.image_empty]
    have e : stepMeanShift A f = caseMean R ∅ (trivialField n) (emptyCoarseState R) (fun _ _ _ _ _ => 0) := by
      unfold stepMeanShift
      congr 1
      funext W Yt ωt bad b
      unfold supportResponseSum
      rw [hS']
      have : weightSupportSites R.params.side R.depth (n * R.params.side) f = ∅ := he
      rw [this]
      simp
    rw [e, caseMean_zero_fn]
    simp [he]
  · have hN := integrable_meanSiteScore hs.majorant hcold hne
    have hM := caseIntegrable_add (caseIntegrable_const_mul (A.responseParams.C₀ * (S.card : ℝ)) hN)
      (caseIntegrable_const_mul (16 * R.params.coupling * (S.card : ℝ)) h1)
    have hb := abs_caseMean_le hs.weights_nonneg (integrable_supportResponseSum hs hcold f hz) hM
      (fun W Yt ωt bad b hl => by
        have := abs_supportResponseSum_le hs (coldCaseGround R (trivialField n)).coarse f hz1 hz W Yt ωt bad b hl
        simpa using this)
    have hE := (hs.majorant _ hcold Unit {()} (fun _ => S) (by simpa using hne)).2
    simp only [Finset.prod_singleton, Finset.card_singleton, pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at hE
    have hq : meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (S.image (parentBlock R.params.side))
        (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2 = 1 := by
      unfold meanSiteScore
      have : ∀ y, siteScore (coarseLabelScore A.responseParams.s₁ A.score) (coldCaseGround R (trivialField n)).state.1
          (coldCaseGround R (trivialField n)).state.2 y = 0 := fun y => by
        unfold siteScore
        rw [dif_neg]
        simp [coldCaseGround, emptyCoarseState]
      simp [this]
    rw [hq, mul_one] at hE
    have hE2 := hE.trans hs.exp_small
    have e1 : stepMeanShift A f = caseMean R (coldCaseGround R (trivialField n)).cut
        (coldCaseGround R (trivialField n)).coarse (coldCaseGround R (trivialField n)).state
        (supportResponseSum A (coldCaseGround R (trivialField n)).coarse f) := rfl
    rw [e1]
    refine hb.trans ?_
    rw [caseMean_add_fn (caseIntegrable_const_mul _ hN) (caseIntegrable_const_mul _ h1), caseMean_const_mul_fn _ hN,
      caseMean_const_mul_fn _ h1, caseMean_one_eq hs.weights_nonneg h1 hs.cold_mass_ne_zero, mul_one]
    have hC : 0 ≤ A.responseParams.C₀ * (S.card : ℝ) := mul_nonneg (by linarith [one_le_C₀ hs]) (Nat.cast_nonneg _)
    have := mul_le_mul_of_nonneg_left hE2 hC
    nlinarith
private theorem abs_centeredStepScore_le (hs : StepHypotheses ch R A n) (V : TorusField n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hz1 : weightNorm R.params.side (R.depth + 1) f ≤ 1) (hz : weightNorm R.params.side R.depth f ≤ 1)
    (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    |centeredStepScore A V f W b| ≤ 2 * (A.responseParams.C₀ *
      ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ)) := by
  classical
  have h1 := abs_weightedScoreTerm_le A hs.bondScores hs.blockMeans hs.admissible hs.response.abs_coeff_le V f hz1 W b
  have h2 := abs_stepMeanShift_le hs f hz1 hz
  have hc : ((weightSupportSites R.params.side (R.depth + 1) n f).card : ℝ) ≤
      ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ) := by
    rw [← image_weightSupportSites]
    exact_mod_cast Finset.card_image_le
  have ha : 1 ≤ R.params.coupling := hs.admissible.a_ge
  have hC := C₀_ge hs
  have e : centeredStepScore A V f W b = weightedScoreTerm A V f W b - stepMeanShift A f := rfl
  rw [e]
  have h3 : 16 * R.params.coupling * ((weightSupportSites R.params.side (R.depth + 1) n f).card : ℝ) ≤
      16 * R.params.coupling * ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  refine (abs_sub _ _).trans ?_
  nlinarith
end Means
section Above
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n] {ch : ℝ}
private theorem one_le_finset_prod {ι : Type} (S : Finset ι) (g : ι → ℝ) (h : ∀ i ∈ S, 1 ≤ g i) :
    1 ≤ ∏ i ∈ S, g i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk]
    have h1 := h k (Finset.mem_insert_self _ _)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    nlinarith
open Classical in
private theorem majorant_of_subset_index (hs : StepHypotheses ch R A n) {G : GasGround R n}
    (hg : G.IsAdmissibleGround) {ι : Type} (I J : Finset ι) (hJ : J ⊆ I)
    (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    CaseIntegrable R G.cut G.coarse G.state
        (fun _ Yt ωt _ _ => ∏ i ∈ J,
          meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) (f i)) Yt ωt) ∧
      caseMean R G.cut G.coarse G.state
          (fun _ Yt ωt _ _ => ∏ i ∈ J,
            meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) (f i)) Yt ωt) ≤
        Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * ch * R.coupling))) *
          ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
            (weightSupportSites R.params.side (R.depth + 1) n (f i)) G.state.1 G.state.2 := by
  set J' := J.filter fun i => (weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).Nonempty with hJ'
  have hsub : J' ⊆ I := (Finset.filter_subset _ _).trans hJ
  have hprod : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      ∏ i ∈ J, meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) (f i)) Yt ωt =
        ∏ i ∈ J', meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) (f i)) Yt ωt :=
    fun Yt ωt => by
    refine (Finset.prod_subset (Finset.filter_subset _ _) fun i hi hn => ?_).symm
    have : weightSupportSites R.params.side R.depth (n * R.params.side) (f i) = ∅ := by
      by_contra hne
      exact hn (Finset.mem_filter.mpr ⟨hi, Finset.nonempty_iff_ne_empty.mpr hne⟩)
    rw [this, meanSiteScore_empty]
  have hm := hs.majorant G hg ι J' (fun i => weightSupportSites R.params.side R.depth (n * R.params.side) (f i))
    fun i hi => (Finset.mem_filter.mp hi).2
  simp only [hprod]
  refine ⟨hm.1, hm.2.trans ?_⟩
  have hnn : ∀ i, 1 ≤ meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
      (weightSupportSites R.params.side (R.depth + 1) n (f i)) G.state.1 G.state.2 := fun i => by
    exact one_le_meanSiteScore (coarseLabelScore_nonneg hs) _ _ _
  have himg : ∀ i, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
      ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).image (parentBlock R.params.side))
        G.state.1 G.state.2 =
      meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
        (weightSupportSites R.params.side (R.depth + 1) n (f i)) G.state.1 G.state.2 := fun i => by
    rw [image_weightSupportSites]
  simp only [himg]
  have hexp : Real.exp (2 ^ J'.card * (J'.card.factorial : ℝ) * Real.exp (-(7 * ch * R.coupling))) ≤
      Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * ch * R.coupling))) := by
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    have hc : J'.card ≤ I.card := Finset.card_le_card hsub
    have h1 : (2 : ℝ) ^ J'.card ≤ 2 ^ I.card := pow_le_pow_right₀ (by norm_num) hc
    have h2 : (J'.card.factorial : ℝ) ≤ I.card.factorial := by exact_mod_cast Nat.factorial_le hc
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
  have hpJ : 1 ≤ ∏ i ∈ J', meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
      (weightSupportSites R.params.side (R.depth + 1) n (f i)) G.state.1 G.state.2 :=
    one_le_finset_prod _ _ fun i _ => hnn i
  have hprodI : ∏ i ∈ J', meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
      (weightSupportSites R.params.side (R.depth + 1) n (f i)) G.state.1 G.state.2 ≤
      ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
        (weightSupportSites R.params.side (R.depth + 1) n (f i)) G.state.1 G.state.2 := by
    rw [← Finset.prod_sdiff hsub]
    have := one_le_finset_prod (I \ J') _ fun i _ => hnn i
    nlinarith
  exact mul_le_mul hexp hprodI (by linarith) (Real.exp_pos _).le
open Classical in
private theorem nextStageBound (hs : StepHypotheses ch R A n) {G : GasGround R n} (hg : G.IsAdmissibleGround)
    (hp : coarseStateWeight R G.cut G.coarse G.state ≠ 0)
    {ι : Type} (I : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hz1 : ∀ i ∈ I, weightNorm R.params.side (R.depth + 1) (f i) ≤ 1)
    (hz : ∀ i ∈ I, weightNorm R.params.side R.depth (f i) ≤ 1)
    (Gm : Finset ι → (W : TorusField (n * R.params.side)) → (Yt : Finset (TorusSite (n * R.params.side))) →
      (Yt → R.labels.Ω) → ℝ) (Err : Finset ι → ℝ)
    (hGm : ∀ J ⊆ I, ∀ Yt, LiveMeasurable R (n * R.params.side) Yt fun p => Gm J p.1 Yt p.2)
    (hIH : ∀ J ⊆ I, ∀ W Yt ωt, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |Gm J W Yt ωt - ∏ i ∈ J, supportResponseTotal A (f i) W Yt ωt| ≤
        Err J * ∏ i ∈ J,
          meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) (f i)) Yt ωt)
    (hErr : ∀ J ⊆ I, 0 ≤ Err J) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hOne : (∀ i ∈ I, (weightSupportSites R.params.side (R.depth + 1) n (f i)).Nonempty) →
      |caseMean R G.cut G.coarse G.state
          (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse A G.coarse (f i) W Yt ωt bad b) -
        ∏ i ∈ I, caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse (f i))| ≤ Δ) :
    |∑ J ∈ I.powerset, caseMean R G.cut G.coarse G.state
        (fun W Yt ωt _ b => Gm J W Yt ωt * ∏ i ∈ I \ J, centeredStepScore A G.coarse (f i) W b) -
        ∏ i ∈ I, ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n (f i),
          (caseMean R G.cut G.coarse G.state (caseResponse A G.coarse Y (f i)) -
          caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) Y (f i)))| ≤
      Δ + (∑ J ∈ I.powerset, Err J * ∏ i ∈ I \ J, (2 * (A.responseParams.C₀ *
        ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)))) *
        (Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * ch * R.coupling))) *
          ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
            (weightSupportSites R.params.side (R.depth + 1) n (f i)) G.state.1 G.state.2) := by
  have hC := one_le_C₀ hs
  have hκ : ∀ i, 0 ≤ A.responseParams.C₀ *
      ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ) := fun i =>
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hrow := hs.expansions
  have hblk := hs.block_side
  have hlev := stageStepMomentBound (C := G.cut) (V := G.coarse) (q := G.state) hs.weights_nonneg I
    (fun i W Yt ωt => supportResponseTotal A (f i) W Yt ωt) (fun i W b => centeredStepScore A G.coarse (f i) W b)
    (fun i Yt ωt => meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) (f i)) Yt ωt)
    Gm Err
    (fun i => A.responseParams.C₀ * ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ))
    (fun i => 2 * (A.responseParams.C₀ *
      ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)))
    (Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * ch * R.coupling))) *
      ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
        (weightSupportSites R.params.side (R.depth + 1) n (f i)) G.state.1 G.state.2)
    (fun Yt => measurableSet_live hrow hblk Yt) (integrable_one hs.majorant hg)
    (fun J hJ => (majorant_of_subset_index hs hg I J hJ f).1) (fun J hJ => (majorant_of_subset_index hs hg I J hJ f).2)
    (fun i Yt ωt => by
      have := one_le_meanSiteScore (n := n * R.params.side) hs.response.price.nonneg
        (weightSupportSites R.params.side R.depth (n * R.params.side) (f i)) Yt ωt
      linarith)
    hκ (fun i => by linarith [hκ i])
    (fun i hi W b => abs_centeredStepScore_le hs G.coarse (f i) (hz1 i hi) (hz i hi) W b)
    (fun i hi W Yt ωt hl => abs_supportResponseTotal_le A hs.response hC hblk (f i) (hz i hi) W Yt ωt hl)
    (fun i Yt => liveMeasurable_supportResponseTotal hrow hs.response hblk Yt (f i)) hGm
    (fun i b => ?_) hIH hErr
  · have e : (fun W Yt ωt (_ : Finset (TorusBond (n * R.params.side))) b =>
        ∏ i ∈ I, (supportResponseTotal A (f i) W Yt ωt + centeredStepScore A G.coarse (f i) W b)) =
        fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse A G.coarse (f i) W Yt ωt bad b := by
      funext W Yt ωt bad b
      refine Finset.prod_congr rfl fun i _ => ?_
      show supportResponseTotal A (f i) W Yt ωt + (weightedScoreTerm A G.coarse (f i) W b - stepMeanShift A (f i)) =
        (supportResponseTotal A (f i) W Yt ωt + weightedScoreTerm A G.coarse (f i) W b) - stepMeanShift A (f i)
      ring
    rw [e] at hlev
    have hmean : ∏ i ∈ I, ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n (f i),
          (caseMean R G.cut G.coarse G.state (caseResponse A G.coarse Y (f i)) -
          caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) Y (f i))) =
        ∏ i ∈ I, caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse (f i)) :=
      Finset.prod_congr rfl fun i hi => (caseMean_centeredSupportResponse hs hg hp (f i) (hz i hi)).symm
    rw [hmean]
    have hdiff : |caseMean R G.cut G.coarse G.state
          (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse A G.coarse (f i) W Yt ωt bad b) -
        ∏ i ∈ I, caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse (f i))| ≤ Δ := by
      by_cases hne : ∀ i ∈ I, (weightSupportSites R.params.side (R.depth + 1) n (f i)).Nonempty
      · exact hOne hne
      · obtain ⟨i₀, hi₀, hem'⟩ : ∃ i ∈ I, weightSupportSites R.params.side (R.depth + 1) n (f i) = ∅ := by
          by_contra hc
          exact hne fun i hi => Finset.nonempty_iff_ne_empty.mpr fun h => hc ⟨i, hi, h⟩
        have hem₂ : weightSupportSites R.params.side R.depth (n * R.params.side) (f i₀) = ∅ := by
          have := image_weightSupportSites (L := R.params.side) (t := R.depth) (n := n) (f i₀)
          rw [hem'] at this
          exact Finset.image_eq_empty.mp this
        have hX : ∀ V W Yt ωt bad b, centeredSupportResponse A V (f i₀) W Yt ωt bad b = 0 :=
          fun V W Yt ωt bad b => by
          have hr : ∀ V' W' Yt' ωt' bad' b', supportResponseSum A V' (f i₀) W' Yt' ωt' bad' b' = 0 :=
            fun V' W' Yt' ωt' bad' b' => by
            unfold supportResponseSum
            rw [hem', hem₂]
            simp
          unfold centeredSupportResponse
          rw [hr]
          have : caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) (f i₀)) = 0 := by
            have e0 : supportResponseSum A (trivialField n) (f i₀) = fun _ _ _ _ _ => 0 := by
              funext W' Yt' ωt' bad' b'
              exact hr _ _ _ _ _ _
            rw [e0]
            exact caseMean_zero_fn
          rw [this]
          simp
        have e1 : (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse A G.coarse (f i) W Yt ωt bad b) =
            fun _ _ _ _ _ => (0 : ℝ) := by
          funext W Yt ωt bad b
          exact Finset.prod_eq_zero hi₀ (hX _ _ _ _ _ _)
        have e2 : ∏ i ∈ I, caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse (f i)) = 0 := by
          refine Finset.prod_eq_zero hi₀ ?_
          have e3 : centeredSupportResponse A G.coarse (f i₀) = fun _ _ _ _ _ => 0 := by
            funext W Yt ωt bad b
            exact hX _ _ _ _ _ _
          rw [e3]
          exact caseMean_zero_fn
        rw [e1, e2, caseMean_zero_fn]
        simpa using hΔ
    have htri := abs_sub_le (∑ J ∈ I.powerset, caseMean R G.cut G.coarse G.state (fun W Yt ωt _ b => Gm J W Yt ωt *
        ∏ i ∈ I \ J, centeredStepScore A G.coarse (f i) W b))
      (caseMean R G.cut G.coarse G.state
        (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse A G.coarse (f i) W Yt ωt bad b))
      (∏ i ∈ I, caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse (f i)))
    linarith
  · have hm := measurable_weightedScoreTerm A hs.bondScores hs.admissible G.coarse (f i) b
    exact show Measurable fun W : TorusField (n * R.params.side) =>
        weightedScoreTerm A G.coarse (f i) W b - stepMeanShift A (f i) from
      hm.sub_const _
end Above
section Levels
variable {ℓ : StepParameters} (hL : ∀ c : ChainStage ℓ, ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup) (lam ch : ℝ) (x : ℕ → ℝ)
  (z₀ : StageWithResponse ℓ)
def StepDecorrelationBound (Cc : ℕ → ℝ) (R : StepSetup) (A : ResponseSetup R) : Prop :=
  ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → ∀ {ι : Type} (I : Finset ι)
    (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (D : ℕ), (∀ i ∈ I, weightNorm R.params.side (R.depth + 1) (f i) ≤ 1) →
    (∀ i ∈ I, (weightSupportSites R.params.side (R.depth + 1) n (f i)).Nonempty) → 2 ^ 10 * R.range ≤ D → 8 < D →
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ Y ∈ thickening 2 (weightSupportSites R.params.side (R.depth + 1) n (f i)),
      ∀ Y' ∈ thickening 2 (weightSupportSites R.params.side (R.depth + 1) n (f j)), D ≤ supDist Y Y') →
    |caseMean R G.cut G.coarse G.state
        (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse A G.coarse (f i) W Yt ωt bad b) -
        ∏ i ∈ I, caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse (f i))| ≤
      Cc I.card * (∑ i ∈ I, ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)) ^ 2 *
        Real.exp (-(R.params.rt * D / 2 ^ 7)) *
        ∏ i ∈ I, (4 * (A.responseParams.C₀ *
          ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)) *
          meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
            (weightSupportSites R.params.side (R.depth + 1) n (f i)) G.state.1 G.state.2)
private theorem separatedAlong_mono {ι : Type} {I J : Finset ι} (hJ : J ⊆ I) (D : ℕ → ℕ) :
    ∀ (u n : ℕ) [NeZero n] (f : ι → StageWeight hL lam x z₀ u n), SeparatedAlong hL lam x z₀ I D u n f →
      SeparatedAlong hL lam x z₀ J D u n f
  | 0, _, _, _, _ => trivial
  | u + 1, n, _, f, h => by
    have h' : SeparatedAlong hL lam x z₀ I D u (n * ℓ.side) f ∧ 2 ^ 10 * (stageStep hL lam x z₀ u).range ≤ D u ∧
        8 < D u ∧ ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ∀ Y ∈ thickening 2 (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f i)),
        ∀ Y' ∈ thickening 2 (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f j)),
          D u ≤ supDist Y Y' := h
    exact ⟨separatedAlong_mono hJ D u (n * ℓ.side) f h'.1, h'.2.1, h'.2.2.1,
      fun i hi j hj => h'.2.2.2 i (hJ hi) j (hJ hj)⟩
open Classical in
private theorem momentError_bound (Cc : ℕ → ℝ) (hCc : ∀ p, 0 ≤ Cc p) (s : ℕ)
    (hF : ∀ u < s, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n →
      StepHypotheses ch (stageStep hL lam x z₀ u) (stageResponse hL lam x z₀ u) n)
    (hO : ∀ u < s, StepDecorrelationBound Cc (stageStep hL lam x z₀ u) (stageResponse hL lam x z₀ u))
    (hG : ∀ u < s, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n))
      (ω : Y → (stageStep hL lam x z₀ (u + 1)).labels.Ω),
      IsLiveState ℓ (stageStep hL lam x z₀ (u + 1)).coupling (stageStep hL lam x z₀ (u + 1)).labelWeight W Y ω →
      (hotCaseGround (stageStep hL lam x z₀ u) W ⟨Y, ω⟩).IsAdmissibleGround ∧
        coarseStateWeight (stageStep hL lam x z₀ u) (hotCoreSites (stageStep hL lam x z₀ u) W) W ⟨Y, ω⟩ ≠ 0)
    (hB : ∀ u ≤ s, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ {ι : Type} (I : Finset ι)
      (f : ι → StageWeight hL lam x z₀ u n) (Y : Finset (TorusSite n)),
      LiveMeasurable (stageStep hL lam x z₀ u) n Y fun p => jointMoment hL lam x z₀ u n I f p.1 Y p.2) :
    ∀ u ≤ s, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ {ι : Type} (I : Finset ι) (D : ℕ → ℕ)
      (f : ι → StageWeight hL lam x z₀ u n), (∀ i ∈ I, weightNorm ℓ.side (stageStep hL lam x z₀ u).depth (f i) ≤ 1) →
      SeparatedAlong hL lam x z₀ I D u n f →
      0 ≤ momentError hL lam x z₀ ch Cc D u n I f ∧
      ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → (stageStep hL lam x z₀ u).labels.Ω),
        IsLiveState ℓ (stageStep hL lam x z₀ u).coupling (stageStep hL lam x z₀ u).labelWeight W Y ω →
        |jointMoment hL lam x z₀ u n I f W Y ω -
            ∏ i ∈ I, supportResponseTotal (stageResponse hL lam x z₀ u) (f i) W Y ω| ≤
          momentError hL lam x z₀ ch Cc D u n I f *
            ∏ i ∈ I, meanSiteScore (stageResponse hL lam x z₀ u).score
              (weightSupportSites ℓ.side (stageStep hL lam x z₀ u).depth n (f i)) Y ω := by
  intro u
  induction u with
  | zero =>
    intro _ n _ hn ι I D f hsz hap
    refine ⟨le_of_eq rfl, fun W Y ω hl => ?_⟩
    have e : jointMoment hL lam x z₀ 0 n I f W Y ω =
        ∏ i ∈ I, supportResponseTotal (stageResponse hL lam x z₀ 0) (f i) W Y ω := rfl
    have e0 : momentError hL lam x z₀ ch Cc D 0 n I f = 0 := rfl
    rw [e, e0]
    simp
  | succ u ih =>
    intro hu n _ hn ι I D f hsz hap
    have hus : u < s := hu
    have hFu := hF u hus n hn
    have hap' : SeparatedAlong hL lam x z₀ I D u (n * ℓ.side) f ∧ 2 ^ 10 * (stageStep hL lam x z₀ u).range ≤ D u ∧
        8 < D u ∧ ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ∀ Y ∈ thickening 2 (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f i)),
        ∀ Y' ∈ thickening 2 (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f j)),
          D u ≤ supDist Y Y' := hap
    obtain ⟨hap0, hr, h8, hsep⟩ := hap'
    have hnb : IsBlockTorusSide ℓ (n * ℓ.side) := hFu.block_side
    have hsz1 : ∀ i ∈ I, weightNorm ℓ.side ((stageStep hL lam x z₀ u).depth + 1) (f i) ≤ 1 := hsz
    have hz : ∀ i ∈ I, weightNorm ℓ.side (stageStep hL lam x z₀ u).depth (f i) ≤ 1 := fun i hi =>
      (weightNorm_mono (NeZero.one_le) _ _).trans (hsz1 i hi)
    have hIHJ : ∀ J ⊆ I, _ := fun J (hJ : J ⊆ I) => ih (Nat.le_of_succ_le hu) (n * ℓ.side) hnb J D f
      (fun i hi => hz i (hJ hi)) (separatedAlong_mono hL lam x z₀ hJ D u (n * ℓ.side) f hap0)
    have hErr : ∀ J ⊆ I, 0 ≤ momentError hL lam x z₀ ch Cc D u (n * ℓ.side) J f := fun J hJ => (hIHJ J hJ).1
    have hC := one_le_C₀ hFu
    have hκ : ∀ i, 0 ≤ (stageResponse hL lam x z₀ u).responseParams.C₀ *
        ((weightSupportSites ℓ.side (stageStep hL lam x z₀ u).depth (n * ℓ.side) (f i)).card : ℝ) := fun i =>
      mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have eE : momentError hL lam x z₀ ch Cc D (u + 1) n I f =
        Cc I.card * (∑ i ∈ I,
          ((weightSupportSites ℓ.side (stageStep hL lam x z₀ u).depth (n * ℓ.side) (f i)).card : ℝ)) ^ 2 *
          Real.exp (-(ℓ.rt * D u / 2 ^ 7)) *
          (∏ i ∈ I, (4 * ((stageResponse hL lam x z₀ u).responseParams.C₀ *
            ((weightSupportSites ℓ.side (stageStep hL lam x z₀ u).depth (n * ℓ.side) (f i)).card : ℝ)))) +
        Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * ch * (stageStep hL lam x z₀ u).coupling))) *
          ∑ J ∈ I.powerset, momentError hL lam x z₀ ch Cc D u (n * ℓ.side) J f *
            ∏ i ∈ I \ J, (2 * ((stageResponse hL lam x z₀ u).responseParams.C₀ *
              ((weightSupportSites ℓ.side (stageStep hL lam x z₀ u).depth (n * ℓ.side) (f i)).card : ℝ))) := rfl
    have hP4 : 0 ≤ ∏ i ∈ I, (4 * ((stageResponse hL lam x z₀ u).responseParams.C₀ *
        ((weightSupportSites ℓ.side (stageStep hL lam x z₀ u).depth (n * ℓ.side) (f i)).card : ℝ))) :=
      Finset.prod_nonneg fun i _ => by linarith [hκ i]
    have hSumE : 0 ≤ ∑ J ∈ I.powerset, momentError hL lam x z₀ ch Cc D u (n * ℓ.side) J f *
        ∏ i ∈ I \ J, (2 * ((stageResponse hL lam x z₀ u).responseParams.C₀ *
          ((weightSupportSites ℓ.side (stageStep hL lam x z₀ u).depth (n * ℓ.side) (f i)).card : ℝ))) :=
      Finset.sum_nonneg fun J hJ => mul_nonneg (hErr J (Finset.mem_powerset.mp hJ))
        (Finset.prod_nonneg fun i _ => by linarith [hκ i])
    refine ⟨?_, fun W Y ω hl => ?_⟩
    · rw [eE]
      exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hCc _) (sq_nonneg _)) (Real.exp_pos _).le) hP4)
        (mul_nonneg (Real.exp_pos _).le hSumE)
    · obtain ⟨hg, hp⟩ := hG u hus n hn W Y ω hl
      have hNq : ∀ i, 0 ≤ meanSiteScore (coarseLabelScore (stageResponse hL lam x z₀ u).responseParams.s₁
          (stageResponse hL lam x z₀ u).score)
          (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f i)) Y ω := fun i => by
        have := one_le_meanSiteScore (coarseLabelScore_nonneg hFu)
          (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f i)) Y ω
        linarith
      have hΔ : 0 ≤ Cc I.card * (∑ i ∈ I,
          ((weightSupportSites ℓ.side (stageStep hL lam x z₀ u).depth (n * ℓ.side) (f i)).card : ℝ)) ^ 2 *
          Real.exp (-(ℓ.rt * D u / 2 ^ 7)) *
          ∏ i ∈ I, (4 * ((stageResponse hL lam x z₀ u).responseParams.C₀ *
            ((weightSupportSites ℓ.side (stageStep hL lam x z₀ u).depth (n * ℓ.side) (f i)).card : ℝ)) *
            meanSiteScore (coarseLabelScore (stageResponse hL lam x z₀ u).responseParams.s₁
              (stageResponse hL lam x z₀ u).score)
              (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f i)) Y ω) :=
        mul_nonneg (mul_nonneg (mul_nonneg (hCc _) (sq_nonneg _)) (Real.exp_pos _).le)
          (Finset.prod_nonneg fun i _ => mul_nonneg (by linarith [hκ i]) (hNq i))
      have hres := nextStageBound hFu hg hp I f hsz1 hz
        (fun J W' Yt ωt => jointMoment hL lam x z₀ u (n * ℓ.side) J f W' Yt ωt)
        (fun J => momentError hL lam x z₀ ch Cc D u (n * ℓ.side) J f)
        (fun J _ Yt => hB u (Nat.le_of_succ_le hu) (n * ℓ.side) hnb J f Yt)
        (fun J hJ W' Yt ωt hl' => (hIHJ J hJ).2 W' Yt ωt hl') hErr _ hΔ
        (fun hne => hO u hus n _ hg I f (D u) hsz1 hne hr h8 hsep)
      have e1 : jointMoment hL lam x z₀ (u + 1) n I f W Y ω = ∑ J ∈ I.powerset,
          caseMean (stageStep hL lam x z₀ u) (hotCoreSites (stageStep hL lam x z₀ u) W) W ⟨Y, ω⟩
            fun W' Yt ωt _ b => jointMoment hL lam x z₀ u (n * ℓ.side) J f W' Yt ωt *
              ∏ i ∈ I \ J, centeredStepScore (stageResponse hL lam x z₀ u) W (f i) W' b := rfl
      have e2 : ∀ i, supportResponseTotal (stageResponse hL lam x z₀ (u + 1)) (f i) W Y ω =
          ∑ Y' ∈ weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f i),
            (caseMean (stageStep hL lam x z₀ u) (hotCoreSites (stageStep hL lam x z₀ u) W) W ⟨Y, ω⟩
                (caseResponse (stageResponse hL lam x z₀ u) W Y' (f i)) -
              caseMean (stageStep hL lam x z₀ u) ∅ (trivialField n) (emptyCoarseState (stageStep hL lam x z₀ u))
                (caseResponse (stageResponse hL lam x z₀ u) (trivialField n) Y' (f i))) := fun i => rfl
      rw [e1]
      simp only [e2]
      refine hres.trans (le_of_eq ?_)
      rw [eE, Finset.prod_mul_distrib]
      have e3 : (stageResponse hL lam x z₀ (u + 1)).score =
          coarseLabelScore (stageResponse hL lam x z₀ u).responseParams.s₁ (stageResponse hL lam x z₀ u).score := rfl
      change _ = _ * ∏ i ∈ I, meanSiteScore (coarseLabelScore (stageResponse hL lam x z₀ u).responseParams.s₁
          (stageResponse hL lam x z₀ u).score)
              (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f i)) Y ω
      change _ * _ * _ * (_ * ∏ i ∈ I, meanSiteScore (coarseLabelScore
          (stageResponse hL lam x z₀ u).responseParams.s₁ (stageResponse hL lam x z₀ u).score)
              (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f i)) Y ω) +
        _ * (_ * ∏ i ∈ I, meanSiteScore (coarseLabelScore (stageResponse hL lam x z₀ u).responseParams.s₁
          (stageResponse hL lam x z₀ u).score)
              (weightSupportSites ℓ.side ((stageStep hL lam x z₀ u).depth + 1) n (f i)) Y ω) = _
      ring
end Levels
section Assembly
private theorem gasRate_pos (T : ParameterAssignment) (hT : T.Admissible) : 0 < T.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
private theorem exp_two_exp_neg_le {v : ℝ} (hv : 5 ≤ v) : Real.exp (2 * Real.exp (-v)) ≤ 11 / 10 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h5 : (32 : ℝ) ≤ Real.exp 5 := by
    have e : Real.exp 5 = Real.exp 1 ^ 5 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 5
  have h6 : Real.exp (-v) ≤ 1 / 32 := by
    have h7 : Real.exp (-v) ≤ Real.exp (-5) := Real.exp_le_exp.mpr (by linarith)
    have h8 : Real.exp (-5) * Real.exp 5 = 1 := by
      rw [← Real.exp_add]
      simp
    have h9 := Real.exp_pos (-5 : ℝ)
    nlinarith
  have hp := Real.exp_pos (-v)
  obtain ⟨u, hu⟩ : ∃ u, u = 2 * Real.exp (-v) := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu1 : u ≤ 1 / 16 := by rw [hu]; linarith
  have h7 := Real.add_one_le_exp (-u)
  have h8 : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  have h9 := Real.exp_pos u
  nlinarith
private theorem cutoff_nonneg {ρ : ℝ} {p : ℝ → ℝ} (hc : ColdStepAtMirrorFrames.IsCutoff ρ p) (hρ : 0 < ρ) {u : ℝ}
    (h0 : 0 ≤ u) (h1 : u < ρ) : 0 ≤ p u := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.cutoff_nonneg <;> assumption
private theorem stepWeightsNonneg_of (hK : BondKernelProperties) {R : StepSetup} (hF : R.IsWellPosed) {n : ℕ}
    [NeZero n] (hb : IsBlockTorusSide R.params (n * R.params.side)) : StepWeightsNonneg R n where
  labelWeight_nonneg W Yt ωt h := hF.hasExpansions.2.nonneg (n * R.params.side) hb W Yt ωt h
  factor_nonneg C V W bad b := by
    have hρ : 0 < R.ballRadius := by
      unfold StepSetup.ballRadius
      have := hF.admissible.σ_pos
      positivity
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · unfold baseLaw
      split_ifs
      · positivity
      · exact le_rfl
    · exact Finset.prod_nonneg fun c _ => (hK.2 _ _ _ _ _ _ _).1.le
    · unfold markProduct
      refine Finset.prod_nonneg fun b' _ => ?_
      have hm : 0 ≤ bondMark R V W b' ∧ bondMark R V W b' ≤ 1 := by
        unfold bondMark ColdStepAtMirrorFrames.cutoffFactor
        split_ifs with h
        · refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
          have := cutoff_nonneg hF.isCutoff hρ (norm_nonneg _) h
          linarith
        · exact ⟨le_rfl, zero_le_one⟩
      split_ifs
      · linarith [hm.2]
      · exact hm.1
private theorem trivialField_isCold {s : ℝ} (hs : 0 < s) (n : ℕ) : IsCold s (trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
end Assembly
theorem severalSupportsMoment_of_steps (hOne : severalSupportsStepDecorrelation)
    (hMaj : productMeanScoreStepBound) (hBor : jointMomentMeasurableStatement) (hForm : StagesAreWellPosed)
    (hGr : HullStateIsHotCase) (hCold : coldFieldStateStatement) (hSc : BondScoreProperties)
    (hWN : WeightsCloseToBlockMeans) (hKer : BondKernelProperties) : severalSupportsMomentStatement := by
  obtain ⟨r1, r1p, h1⟩ := hOne
  obtain ⟨r2, r2p, h2⟩ := hMaj
  obtain ⟨r3, r3p, h3⟩ := hBor
  refine ⟨fun c => min (r1 c) (min (r2 c) (r3 c)), fun c => lt_min (r1p c) (lt_min (r2p c) (r3p c)),
    fun T hT hrt K => ?_⟩
  have hr1 : T.rt ≤ r1 T.toChainParameters := hrt.trans (min_le_left _ _)
  have hr2 : T.rt ≤ r2 T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr3 : T.rt ≤ r3 T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y1, H1⟩ := h1 T hT hr1 K
  obtain ⟨y2, H2⟩ := h2 T hT hr2 K
  obtain ⟨y3, H3⟩ := h3 T hT hr3 K
  obtain ⟨y4, H4⟩ := hForm T hT
  obtain ⟨y5, H5⟩ := hGr T hT
  choose Cf hCf using H1
  have hch := gasRate_pos T hT
  refine ⟨max y1 (max y2 (max y3 (max y4 (max y5 (5 / (7 * T.gasRate)))))), fun p => max (Cf p) 0,
    fun p => le_max_right _ _, ?_⟩
  intro y β hL z₀ hy hFirst s hStand n _ hn ι I D f hsz hap W Y ω hl
  have hy1 : y1 ≤ y := (le_max_left _ _).trans hy
  have hy2 : y2 ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy3 : y3 ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hy4 : y4 ≤ y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have hy5 : y5 ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))).trans hy
  have hy6 : 5 / (7 * T.gasRate) ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))).trans hy
  have hFS := H4 y hy4 K β hL z₀ hFirst s hStand
  have hFacts : ∀ u < s, ∀ (m : ℕ) [NeZero m], IsBlockTorusSide (T.stepParameters y) m →
      StepHypotheses T.gasRate (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u)
        (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) m := by
    intro u hu m _ hm
    have hst := hStand u hu.le
    have hst' := hStand (u + 1) hu
    have hfs := hFS u hu.le
    have hLp : 1 ≤ (T.stepParameters y).side := NeZero.one_le
    have hm0 : 0 < m := NeZero.pos m
    have hn0 : (T.stepParameters y).n₀ ≤ m := le_trans (Nat.le_mul_of_pos_left _ hLp) hm.2
    have hblk : IsBlockTorusSide (T.stepParameters y) (m * (T.stepParameters y).side) :=
      ⟨Dvd.intro_left _ rfl, hm.2.trans (Nat.le_mul_of_pos_right _ hLp)⟩
    refine ⟨stepWeightsNonneg_of hKer hfs hblk, hfs.hasExpansions, hfs.admissible, hst.onFamily.admissible, hblk, ?_,
      hSc, hWN, ?_, ?_, ?_⟩
    · exact fun G hg ι I B hB => H2 y hy2 _ _ hst.params_eq hst.onFamily m G hg ι I B hB
    · exact Or.inl ⟨hn0, trivialField_isCold (by have := hfs.admissible.σ_pos; positivity) m, rfl, rfl, rfl⟩
    · intro h0
      have e1 := (hCold _ hfs m hn0).1 (trivialField m) (fun z => absurd z.2 (Finset.notMem_empty _))
      have e2 : 0 < kernelImage (T.stepParameters y)
          (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).coupling
          (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).functional m (trivialField m) :=
        hst'.onFamily.onFamily.isStep.1.1.positive m hn0 (trivialField m) (trivialField_isCold hfs.admissible.σ_pos m)
      have e3 : coarseStateWeight (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) ∅
          (trivialField m) (emptyCoarseState (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u)) =
          kernelImage (T.stepParameters y)
            (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).coupling
            (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).functional m (trivialField m) := e1
      rw [e3] at h0
      exact e2.ne' h0
    · refine exp_two_exp_neg_le ?_
      have hx : y ≤ (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).coupling :=
        hst.onFamily.onFamily.le_coupling
      have h7 : 0 < 7 * T.gasRate := by positivity
      have := (div_le_iff₀ h7).mp (hy6.trans hx)
      linarith
  have hOneB : ∀ u < s, StepDecorrelationBound (fun p => max (Cf p) 0)
      (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u)
      (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) := by
    intro u hu m _ G hg ι I f' D' hz hne hr h8 hsep
    have hst := hStand u hu.le
    have hfs := hFS u hu.le
    have hb := (hCf I.card y hy1 _ _ hst.params_eq hst.onFamily m G hg ι I f' D' rfl hz hne hr h8 hsep).2.2
    rw [← hst.params_eq] at hb
    refine hb.trans ?_
    have hC := one_le_C₀_of_admissible hst.onFamily.admissible hfs.admissible
    have hprod : 0 ≤ ∏ i ∈ I, (4 * ((stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).responseParams.C₀ *
        ((weightSupportSites (T.stepParameters y).side
          (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).depth
          (m * (T.stepParameters y).side) (f' i)).card : ℝ)) *
        meanSiteScore (coarseLabelScore
          (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).responseParams.s₁
          (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).score)
          (weightSupportSites (T.stepParameters y).side
            ((stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).depth + 1) m (f' i))
          G.state.1 G.state.2) :=
      Finset.prod_nonneg fun i _ => by
        have h1 := one_le_meanSiteScore (coarseLabelScore_nonneg_of hst.onFamily.admissible hfs.admissible)
          (weightSupportSites (T.stepParameters y).side
            ((stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).depth + 1) m (f' i))
          G.state.1 G.state.2
        have h2 : (0 : ℝ) ≤ ((weightSupportSites (T.stepParameters y).side
            (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).depth
            (m * (T.stepParameters y).side) (f' i)).card : ℝ) := Nat.cast_nonneg _
        have h3 := mul_nonneg (by linarith :
          0 ≤ (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).responseParams.C₀) h2
        exact mul_nonneg (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (sq_nonneg _)) (Real.exp_pos _).le) hprod
  have hGr' : ∀ u < s, ∀ (m : ℕ) [NeZero m], IsBlockTorusSide (T.stepParameters y) m →
      ∀ (W' : TorusField m) (Y' : Finset (TorusSite m))
      (ω' : Y' → (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ (u + 1)).labels.Ω),
      IsLiveState (T.stepParameters y)
        (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ (u + 1)).coupling
        (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ (u + 1)).labelWeight W' Y' ω' →
      (hotCaseGround (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) W'
          ⟨Y', ω'⟩).IsAdmissibleGround ∧
        coarseStateWeight (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u)
          (hotCoreSites (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) W') W'
          ⟨Y', ω'⟩ ≠ 0 := by
    intro u hu m _ hm W' Y' ω' hl'
    have hst := hStand u hu.le
    have hst' := hStand (u + 1) hu
    obtain ⟨hhull, hpos⟩ := hl'
    have hform := hst'.onFamily.onFamily.isStep.1.2.form m hm W' Y' ω' hhull
    have hne : ∏ X ∈ chainComponents (clusterRange
          (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ (u + 1)).coupling) Y',
        (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ (u + 1)).clusterFactor m W' Y' ω' X ≠ 0 := by
      intro h0
      have h2 : (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ (u + 1)).labelWeight m W' Y' ω' = 0 := by
        rw [show (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ (u + 1)).labelWeight m W' Y' ω' = _
          from hform, h0, mul_zero]
      exact hpos.ne' h2
    have hΦ : ∀ X ∈ chainComponents (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u).nextRange Y',
        coarseFactor W' (⟨Y', ω'⟩ :
          CoarseState (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) m) X ≠ 0 := fun X hX => by
      have h3 := Finset.prod_ne_zero_iff.mp hne X hX
      have e2 : coarseFactorExpansion (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) m W' Y' ω' X =
          coarseFactor W' (⟨Y', ω'⟩ :
            CoarseState (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) m) X := by
        unfold coarseFactorExpansion
        rw [dif_neg (NeZero.ne m)]
      rw [← e2]
      exact h3
    have hot := H5 y hy5 _ hst.onFamily.onFamily (hFS u hu.le) m hm W' ⟨Y', ω'⟩ hhull hΦ
    refine ⟨Or.inr hot, ?_⟩
    have e3 : coarseWeightExpansion (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) m W' Y' ω' =
        coarseStateWeight (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u)
          (hotCoreSites (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) W') W' ⟨Y', ω'⟩ := by
      unfold coarseWeightExpansion
      rw [dif_neg (NeZero.ne m)]
    rw [← e3]
    exact hpos.ne'
  have hB : ∀ u ≤ s, ∀ (m : ℕ) [NeZero m], IsBlockTorusSide (T.stepParameters y) m → ∀ {ι' : Type} (I' : Finset ι')
      (f' : ι' → StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u m) (Y' : Finset (TorusSite m)),
      LiveMeasurable (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u) m Y'
        fun p => jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ u m I' f' p.1 Y' p.2 := by
    intro u hu m _ hm ι' I' f' Y'
    unfold LiveMeasurable
    exact H3 y β hL z₀ hy3 hFirst u (fun t ht => hStand t (ht.trans hu)) m hm I' f' Y'
  exact (momentError_bound hL T.lam T.gasRate (couplingsAlongFlow (T.stepParameters y) β) z₀ (fun p => max (Cf p) 0)
    (fun p => le_max_right _ _) s hFacts hOneB hGr' hB s le_rfl n hn I D f hsz hap).2 W Y ω hl
end MultiScaleMoments
end YangMills.Construction.ResponseInTheExpansion
end
