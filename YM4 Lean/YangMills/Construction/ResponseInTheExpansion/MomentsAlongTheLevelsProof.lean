import YangMills.Construction.LawInAState.WilsonsLawOnTheLeastTorusInTheExpansionProof
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import YangMills.Construction.ResponseInTheExpansion.LevelsFormStates
import YangMills.Construction.ResponseInTheExpansion.MeanOfScoresOverAStep
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheStates
import YangMills.Construction.ResponseInTheExpansion.MomentsAlongTheLevels
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters ClusterExpansionOfAStep
namespace MomentsAlongStages
section Scores
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
private def bondCoefficient (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (c : TorusBond n) : ℝ :=
  R.params.coupling / 2 * A.coeff * ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
    blockMean R.params.side (R.depth + 1) n Y f *
    ∑ i : Fin 4, ((if c = (Y, i) then (1 : ℝ) else 0) + (if c = (Y - unitStep n i, i) then (1 : ℝ) else 0))
private theorem sum_indicator_bonds_mul (s : TorusBond n → ℝ) (Y : TorusSite n) :
    ∑ c : TorusBond n, (∑ i : Fin 4, ((if c = (Y, i) then (1 : ℝ) else 0) +
      (if c = (Y - unitStep n i, i) then (1 : ℝ) else 0))) * s c =
      ∑ i : Fin 4, (s (Y, i) + s (Y - unitStep n i, i)) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_mul, Finset.sum_add_distrib]
private theorem centeredStepScore_eq (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    centeredStepScore A V f W b = -stepMeanShift A f +
      ∑ c : TorusBond n, bondCoefficient A f c * bondScore R.params R.coupling W V b c := by
  unfold centeredStepScore bondCoefficient
  have h : ∑ c : TorusBond n, (R.params.coupling / 2 * A.coeff *
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, blockMean R.params.side (R.depth + 1) n Y f *
      ∑ i : Fin 4, ((if c = (Y, i) then (1 : ℝ) else 0) + (if c = (Y - unitStep n i, i) then (1 : ℝ) else 0))) *
        bondScore R.params R.coupling W V b c =
      R.params.coupling / 2 * A.coeff * ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
        blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y := by
    simp_rw [mul_assoc (R.params.coupling / 2 * A.coeff), Finset.sum_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp_rw [mul_assoc (blockMean R.params.side (R.depth + 1) n Y f)]
    rw [← Finset.mul_sum, sum_indicator_bonds_mul]
    rfl
  rw [h]
  ring
private theorem centeredStepScore_measurable_bounded (hT : BondScoreProperties) (hfit : R.params.Admissible)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    (∀ b, Measurable fun p : TorusField (n * R.params.side) × TorusField n => centeredStepScore A p.2 f p.1 b) ∧
      ∃ C : ℝ, ∀ W b V, |centeredStepScore A V f W b| ≤ C := by
  refine ⟨fun b => ?_, |stepMeanShift A f| + ∑ c : TorusBond n, |bondCoefficient A f c| * 2, fun W b V => ?_⟩
  · simp_rw [centeredStepScore_eq]
    refine measurable_const.add (Finset.measurable_fun_sum _ fun c _ => ?_)
    exact ((hT R.params hfit R.coupling n b c).2.2.2.2).const_mul _
  · rw [centeredStepScore_eq]
    refine (abs_add_le _ _).trans (add_le_add (by rw [abs_neg]) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hT R.params hfit R.coupling n b c).2.2.1 W V) (abs_nonneg _)
private theorem stepMean_prod_centeredStepScore {ι : Type} (hS : ScoreProductStepMean) (hfit : R.params.Admissible)
    (I : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ c, bondCoefficient A (f i) c = 0 ∨ bondCoefficient A (f j) c = 0)
    (W : TorusField (n * R.params.side)) :
    ∑ b : BaseChoice R.params.side n, ∫ V, (∏ i ∈ I, centeredStepScore A V (f i) W b) *
      stepTransitionDensity R.params R.coupling W b V ∂(fieldHaar n) =
      ∏ i ∈ I, -stepMeanShift A (f i) := by
  classical
  let e := I.equivFin
  have hp : ∀ g : ι → ℝ, ∏ i ∈ I, g i = ∏ k : Fin I.card, g (e.symm k) := by
    intro g
    rw [← Finset.prod_coe_sort I g]
    exact (Equiv.prod_comp e.symm fun i : I => g i).symm
  have key := hS R.params hfit hfit.depth_lt R.coupling n W I.card (fun k => -stepMeanShift A (f (e.symm k)))
    (fun k c => bondCoefficient A (f (e.symm k)) c) (fun c k k' hk => hsep _ (e.symm k).2 _ (e.symm k').2
      (fun h => hk (e.symm.injective (Subtype.ext h))) c)
  rw [hp fun i => -stepMeanShift A (f i), ← key]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only
  rw [hp fun i => centeredStepScore A V (f i) W b]
  simp_rw [centeredStepScore_eq]
end Scores
section Step
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
private theorem stateIntegralSum_mul_const (H : StateFunction R n) (c : ℝ) :
    stateIntegralSum R n (fun W Y ω => H W Y ω * c) = c * stateIntegralSum R n H := by
  unfold stateIntegralSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [integral_mul_const, mul_comm]
private def StepMeanProperty (R : StepSetup) (h : CoarseLabelFacts R) (lam x'' : ℝ) (n : ℕ) [NeZero n] : Prop :=
  ∀ (g : StateFunction R (n * R.params.side))
    (ψ : TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ),
    IntegrableOnStates R (n * R.params.side) g →
    (∀ b, Measurable fun p : TorusField (n * R.params.side) × TorusField n => ψ p.1 b p.2) →
    (∃ C : ℝ, ∀ W b V, |ψ W b V| ≤ C) →
    IntegrableOnStates (nextStepSetup R h lam x'') n (conditionalCaseMean R g ψ) ∧
    stateIntegralSum (nextStepSetup R h lam x'') n (conditionalCaseMean R g ψ) =
      stateIntegralSum R (n * R.params.side) fun W Yt ωt => g W Yt ωt *
        ∑ b : BaseChoice R.params.side n, ∫ V, ψ W b V * stepTransitionDensity R.params R.coupling W b V ∂(fieldHaar n)
open Classical in
private def stepJointMoment {ι : Type} (I : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (G : Finset ι → StateFunction R (n * R.params.side)) (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) : ℝ :=
  ∑ J ∈ I.powerset, conditionalCaseMean R (G J)
    (fun W b V => ∏ i ∈ I \ J, centeredStepScore A V (f i) W b) V Y ω
open Classical in
private theorem stepJointMoment_integrable_and_eq {ι : Type} (hT : BondScoreProperties) (hS : ScoreProductStepMean)
    (hfit : R.params.Admissible) {h : CoarseLabelFacts R} {lam x'' : ℝ} (hM : StepMeanProperty R h lam x'' n)
    (I : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ c, bondCoefficient A (f i) c = 0 ∨ bondCoefficient A (f j) c = 0)
    (G : Finset ι → StateFunction R (n * R.params.side))
    (hG : ∀ J ∈ I.powerset, IntegrableOnStates R (n * R.params.side) (G J)) :
    IntegrableOnStates (nextStepSetup R h lam x'') n (stepJointMoment A I f G) ∧
    stateIntegralSum (nextStepSetup R h lam x'') n (stepJointMoment A I f G) =
      ∑ J ∈ I.powerset, (∏ i ∈ I \ J, -stepMeanShift A (f i)) * stateIntegralSum R (n * R.params.side) (G J) := by
  have hfacts : ∀ J : Finset ι, (∀ b, Measurable fun p : TorusField (n * R.params.side) × TorusField n =>
      (fun W b V => ∏ i ∈ I \ J, centeredStepScore A V (f i) W b :
        TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ) p.1 b p.2) ∧
      ∃ C : ℝ, ∀ W b V, |(fun W b V => ∏ i ∈ I \ J, centeredStepScore A V (f i) W b :
        TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ) W b V| ≤ C := by
    intro J
    choose C hC using fun i => (centeredStepScore_measurable_bounded A hT hfit (f i)).2
    refine ⟨fun b => Finset.measurable_fun_prod _ fun i _ =>
      (centeredStepScore_measurable_bounded A hT hfit (f i)).1 b, ∏ i ∈ I \ J, C i, fun W b V => ?_⟩
    simp only
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => hC i W b V
  have hone : ∀ J ∈ I.powerset, _ := fun J hJ => hM (G J) _ (hG J hJ) (hfacts J).1 (hfacts J).2
  refine ⟨fun Y => ?_, ?_⟩
  · unfold stepJointMoment
    exact integrable_finsetSum _ fun J hJ => (hone J hJ).1 Y
  · have hE : ∀ J ∈ I.powerset, stateIntegralSum (nextStepSetup R h lam x'') n (conditionalCaseMean R (G J)
        (fun W b V => ∏ i ∈ I \ J, centeredStepScore A V (f i) W b)) =
        (∏ i ∈ I \ J, -stepMeanShift A (f i)) * stateIntegralSum R (n * R.params.side) (G J) := by
      intro J hJ
      rw [(hone J hJ).2, ← stateIntegralSum_mul_const]
      congr 1
      funext W Yt ωt
      rw [stepMean_prod_centeredStepScore A hS hfit (I \ J) f
        (fun i hi j hj => hsep i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1) W]
    rw [← Finset.sum_congr rfl hE]
    unfold stateIntegralSum stepJointMoment
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Y _ => ?_
    exact integral_finsetSum _ fun J hJ => (hone J hJ).1 Y
end Step
section Density
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem stateIntegral_eq_stateIntegralSum (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params n)
    (H : StateFunction R n) (hH : IntegrableOnStates R n H) : stateIntegral R n H = stateIntegralSum R n H := by
  classical
  have hd : ∀ Y : Finset (TorusSite n), Measurable fun p : TorusField n × (Y → R.labels.Ω) =>
      if IsHullState R.params (clusterRange R.coupling) p.1 Y then R.labelWeight n p.1 Y p.2 else 0 :=
    fun Y => (hrow.2.borel n hb Y).1
  have hden : ∀ Y : Finset (TorusSite n), (fun p : TorusField n × (Y → R.labels.Ω) =>
      if IsHullState R.params (clusterRange R.coupling) p.1 Y then ENNReal.ofReal (R.labelWeight n p.1 Y p.2) else 0) =
      fun p => ENNReal.ofReal (if IsHullState R.params (clusterRange R.coupling) p.1 Y
        then R.labelWeight n p.1 Y p.2 else 0) := by
    intro Y
    funext p
    split_ifs <;> simp
  have hdm : ∀ Y : Finset (TorusSite n), Measurable fun p : TorusField n × (Y → R.labels.Ω) =>
      ENNReal.ofReal (if IsHullState R.params (clusterRange R.coupling) p.1 Y then R.labelWeight n p.1 Y p.2 else 0) :=
    fun Y => ENNReal.measurable_ofReal.comp (hd Y)
  have hnn : ∀ (Y : Finset (TorusSite n)) (p : TorusField n × (Y → R.labels.Ω)),
      0 ≤ if IsHullState R.params (clusterRange R.coupling) p.1 Y then R.labelWeight n p.1 Y p.2 else 0 := by
    intro Y p
    split_ifs with hh
    · exact hrow.2.nonneg n hb _ _ _ hh
    · exact le_rfl
  have hint : ∀ Y : Finset (TorusSite n), Integrable (fun p : TorusField n × (Y → R.labels.Ω) =>
      (if IsHullState R.params (clusterRange R.coupling) p.1 Y then R.labelWeight n p.1 Y p.2 else 0) * H p.1 Y p.2)
      ((fieldHaar n).prod (Measure.pi fun _ : Y => R.labels.μ)) := by
    intro Y
    have h1 := hH Y
    unfold stateMeasure at h1
    rw [hden Y, integrable_withDensity_iff_integrable_smul' (hdm Y)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h1
    refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hnn Y p)]
  have hval : ∀ Y : Finset (TorusSite n), ∫ p : TorusField n × (Y → R.labels.Ω), H p.1 Y p.2 ∂(stateMeasure R n Y) =
      ∫ W, ∫ ω, (if IsHullState R.params (clusterRange R.coupling) W Y then R.labelWeight n W Y ω else 0) * H W Y ω
        ∂(Measure.pi fun _ : Y => R.labels.μ) ∂(fieldHaar n) := by
    intro Y
    unfold stateMeasure
    rw [hden Y, integral_withDensity_eq_integral_toReal_smul (hdm Y)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rw [← integral_prod _ (hint Y)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hnn Y p)]
  unfold stateIntegralSum stateIntegral
  simp_rw [hval]
  rw [← integral_finsetSum _ fun Y _ => (hint Y).integral_prod_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  simp only
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun Y _ => ?_
  by_cases hh : IsHullState R.params (clusterRange R.coupling) W Y
  · simp only [if_pos hh]
  · simp [if_neg hh]
end Density
section Weights
variable {m : ℕ} [NeZero m]
private theorem curvatureObservable_continuous (h : PlaquetteWeight m) : Continuous (curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p1196 <;> assumption
private theorem continuous_wilsonBoltzmann (β : ℝ) :
    Continuous fun W : TorusField m => Real.exp (-β * wilsonAction Finset.univ W) := by apply _root_.YangMills.DeltaSharedProofs.p502405 <;> assumption
private theorem isFiniteMeasure_wilsonLaw (β : ℝ) : IsFiniteMeasure (wilsonLaw β m) := by
  unfold wilsonLaw
  refine isFiniteMeasure_withDensity_ofReal ?_
  exact (((continuous_wilsonBoltzmann β).div_const _).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral
private theorem integrable_wilsonLaw_of_continuous (β : ℝ) {F : TorusField m → ℝ} (hF : Continuous F) :
    Integrable F (wilsonLaw β m) := by
  have := isFiniteMeasure_wilsonLaw (m := m) β
  exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end Weights
section Levels
variable {ℓ : StepParameters} (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam : ℝ) (x : ℕ → ℝ)
  (z₀ : StageWithResponse ℓ) (β : ℝ)
private def wilsonCenteredMoment {ι : Type} (s n : ℕ) [NeZero n] (I : Finset ι)
    (f : ι → StageWeight hL lam x z₀ s n) : ℝ :=
  ∫ W, ∏ i ∈ I, (curvatureObservable (f i) W - accumulatedShift hL lam x z₀ s n (f i))
    ∂(wilsonLaw β (fineSide ℓ.side (stageStep hL lam x z₀ s).depth n))
private theorem separatedAlong_mono {ι : Type} {I J : Finset ι} (hJ : J ⊆ I) (D : ℕ → ℕ) :
    ∀ (s n : ℕ) [NeZero n] (f : ι → StageWeight hL lam x z₀ s n), SeparatedAlong hL lam x z₀ I D s n f →
      SeparatedAlong hL lam x z₀ J D s n f
  | 0, _, _, _, _ => trivial
  | s + 1, n, _, f, h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨separatedAlong_mono hJ D s (n * ℓ.side) f h1, h2, h3, fun i hi j hj => h4 i (hJ hi) j (hJ hj)⟩
open Classical in
private theorem wilsonCenteredMoment_succ {ι : Type} (s n : ℕ) [NeZero n] (I : Finset ι)
    (f : ι → StageWeight hL lam x z₀ (s + 1) n) :
    wilsonCenteredMoment hL lam x z₀ β (s + 1) n I f =
      ∑ J ∈ I.powerset, (∏ i ∈ I \ J, -stepMeanShift (stageResponse hL lam x z₀ s) (f i)) *
        wilsonCenteredMoment hL lam x z₀ β s (n * ℓ.side) J f := by
  unfold wilsonCenteredMoment
  have e : ∀ W, ∏ i ∈ I, (curvatureObservable (f i) W - accumulatedShift hL lam x z₀ (s + 1) n (f i)) =
      ∑ J ∈ I.powerset, (∏ i ∈ I \ J, -stepMeanShift (stageResponse hL lam x z₀ s) (f i)) *
        ∏ i ∈ J, (curvatureObservable (f i) W - accumulatedShift hL lam x z₀ s (n * ℓ.side) (f i)) := by
    intro W
    have h := Finset.prod_add
      (fun i => curvatureObservable (f i) W - accumulatedShift hL lam x z₀ s (n * ℓ.side) (f i))
      (fun i => -stepMeanShift (stageResponse hL lam x z₀ s) (f i)) I
    rw [Finset.sum_congr rfl fun J _ => mul_comm _ _] at h
    rw [← h]
    refine Finset.prod_congr rfl fun i _ => ?_
    show _ - (accumulatedShift hL lam x z₀ s (n * ℓ.side) (f i) +
      stepMeanShift (stageResponse hL lam x z₀ s) (f i)) = _
    ring
  simp_rw [e]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun J _ => ?_
    rw [integral_const_mul]
    rfl
  · intro J _
    refine integrable_wilsonLaw_of_continuous β ?_
    refine continuous_const.mul (continuous_finsetProd _ fun i _ => ?_)
    exact (curvatureObservable_continuous _).sub continuous_const
end Levels
section Apart
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
private theorem exists_site_near_of_bondCoefficient_ne_zero
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (c : TorusBond n)
    (h : bondCoefficient A f c ≠ 0) :
    ∃ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, supDist c.1 Y ≤ 1 := by
  by_contra hn
  push Not at hn
  apply h
  unfold bondCoefficient
  rw [Finset.sum_eq_zero, mul_zero]
  intro Y hY
  have hfar := hn Y hY
  have h0 : ∑ i : Fin 4, ((if c = (Y, i) then (1 : ℝ) else 0) +
      (if c = (Y - unitStep n i, i) then (1 : ℝ) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : c ≠ (Y, i) := by
      intro e
      rw [e, supDist_self] at hfar
      omega
    have h2 : c ≠ (Y - unitStep n i, i) := by
      intro e
      have := supDist_add_unitStep_le (Y - unitStep n i) i
      rw [sub_add_cancel] at this
      rw [e] at hfar
      exact absurd hfar (by simpa using this)
    simp [h1, h2]
  rw [h0, mul_zero]
private theorem bondCoefficient_disjoint_of_far {ι : Type} (I : Finset ι)
    (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (d : ℕ) (hd : 8 < d)
    (hA : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ Y ∈ thickening 2 (weightSupportSites R.params.side (R.depth + 1) n (f i)),
      ∀ Y' ∈ thickening 2 (weightSupportSites R.params.side (R.depth + 1) n (f j)), d ≤ supDist Y Y') :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ c, bondCoefficient A (f i) c = 0 ∨ bondCoefficient A (f j) c = 0 := by
  classical
  intro i hi j hj hij c
  by_contra hn
  push Not at hn
  obtain ⟨Y, hY, hcY⟩ := exists_site_near_of_bondCoefficient_ne_zero A _ c hn.1
  obtain ⟨Y', hY', hcY'⟩ := exists_site_near_of_bondCoefficient_ne_zero A _ c hn.2
  have hin : ∀ (S : Finset (TorusSite n)) (z : TorusSite n), z ∈ S → z ∈ thickening 2 S := fun S z hz =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hz, by rw [supDist_self]; omega⟩
  have h1 := hA i hi j hj hij Y (hin _ _ hY) Y' (hin _ _ hY')
  have h2 := supDist_triangle Y c.1 Y'
  rw [supDist_comm Y c.1] at h2
  omega
end Apart
section Bottom
private theorem sum_siteResponse {m : ℕ} [NeZero m] (h : PlaquetteWeight m) (W : TorusField m) :
    ∑ y : TorusSite m, siteResponse y W h = curvatureObservable h W := by
  unfold siteResponse curvatureObservable
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_div]
  have hc : ∀ {α : Type} [Fintype α] [DecidableEq α] (l : List α), ∑ y : α, ((l.count y : ℕ) : ℝ) = l.length := by
    intro α _ _ l
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.count_cons, Nat.cast_add, Finset.sum_add_distrib, ih, List.length_cons, Nat.cast_succ]
      congr 1
      simp
  have h4 : ∑ y : TorusSite m, vertexMultiplicity y p = 4 := by
    have := hc (plaquetteVertices p.1 p.2.1 p.2.2)
    simpa [vertexMultiplicity, plaquetteVertices] using this
  rw [h4]
  ring
abbrev _root_.YangMills.SharedProofs.p40351 := @sum_siteResponse
private theorem siteResponse_trivialField {m : ℕ} [NeZero m] (y : TorusSite m) (h : PlaquetteWeight m) :
    siteResponse y (trivialField m) h = 0 := by
  unfold siteResponse
  refine Finset.sum_eq_zero fun p hp => ?_
  have e0 : plaquetteEnergyOf (trivialField m) p = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => plaquetteEnergy_nonneg _ _ _ _)).mp
      (wilsonAction_trivialField Finset.univ) p hp
  rw [e0, mul_zero, mul_zero]
private theorem sum_support_siteResponse_sub (L : ℕ) [NeZero L] {m : ℕ} [NeZero m] (h : PlaquetteWeight m)
    (W : TorusField m) :
    ∑ y ∈ weightSupportSites L 0 m h, (siteResponse y W h - siteResponse y (trivialField m) h) =
      curvatureObservable h W := by
  classical
  simp_rw [siteResponse_trivialField, sub_zero]
  rw [← sum_siteResponse]
  refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
  unfold siteResponse
  refine Finset.sum_eq_zero fun p hp => ?_
  by_cases h0 : h p = 0
  · simp [h0]
  · have hc : vertexMultiplicity y p = 0 := by
      by_contra hc
      apply hy
      have hm : y ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by
        have : (plaquetteVertices p.1 p.2.1 p.2.2).count y ≠ 0 := by
          intro e
          apply hc
          simp [vertexMultiplicity, e]
        exact List.count_pos_iff.mp (Nat.pos_of_ne_zero this)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, ⟨(Finset.mem_filter.mp hp).2.1, y, hm,
        Finset.mem_singleton_self y⟩, h0⟩
    simp [hc]
abbrev _root_.YangMills.SharedProofs.p55288 := @sum_support_siteResponse_sub
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem stateIntegralSum_of_wilsonWeight (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params n) {β : ℝ}
    (hD : R.functional = wilsonWeight β) :
    (∀ Y, IsFiniteMeasure (stateMeasure R n Y)) ∧ ∀ F : TorusField n → ℝ, Continuous F →
      IntegrableOnStates R n (fun W _ _ => F W) ∧
      stateIntegralSum R n (fun W _ _ => F W) =
        ∫ W, F W * Real.exp (-β * wilsonAction Finset.univ W) ∂(fieldHaar n) := by
  classical
  set e : TorusField n → ℝ := fun W => Real.exp (-β * wilsonAction Finset.univ W) with he
  have hec : Continuous e := continuous_wilsonBoltzmann β
  have hei : Integrable e (fieldHaar n) :=
    hec.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDn : ∀ W, R.functional n W = e W := by
    intro W
    rw [hD]
    simp [wilsonWeight, NeZero.ne n, he]
  have hd : ∀ Y : Finset (TorusSite n), Measurable fun p : TorusField n × (Y → R.labels.Ω) =>
      (if IsHullState R.params (clusterRange R.coupling) p.1 Y
        then ENNReal.ofReal (R.labelWeight n p.1 Y p.2) else 0 : ENNReal) := by
    intro Y
    have h1 := ENNReal.measurable_ofReal.comp (hrow.2.borel n hb Y).1
    convert h1 using 2 with p
    simp only [Function.comp]
    split_ifs <;> simp
  have hsum : ∀ W, ∑ Y : Finset (TorusSite n), ∫⁻ ω, (if IsHullState R.params (clusterRange R.coupling) W Y
      then ENNReal.ofReal (R.labelWeight n W Y ω) else 0)
      ∂(Measure.pi fun _ : Y => R.labels.μ) = ENNReal.ofReal (e W) := by
    intro W
    rw [← hDn, ← hrow.2.sum n hb W, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hh : IsHullState R.params (clusterRange R.coupling) W Y
    · simp only [if_pos hh]
    · simp [if_neg hh]
  have hmeas : (∑ Y : Finset (TorusSite n), (stateMeasure R n Y).map Prod.fst) =
      (fieldHaar n).withDensity fun W => ENNReal.ofReal (e W) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.finsetSum_apply, withDensity_apply _ hA]
    have h1 : ∀ Y : Finset (TorusSite n), ((stateMeasure R n Y).map Prod.fst) A =
        ∫⁻ W, A.indicator 1 W * ∫⁻ ω, (if IsHullState R.params (clusterRange R.coupling) W Y
          then ENNReal.ofReal (R.labelWeight n W Y ω) else 0)
          ∂(Measure.pi fun _ : Y => R.labels.μ) ∂(fieldHaar n) := by
      intro Y
      rw [Measure.map_apply measurable_fst hA]
      unfold stateMeasure
      rw [withDensity_apply _ (measurable_fst hA), ← lintegral_indicator (measurable_fst hA),
        lintegral_prod _ ((hd Y).indicator (measurable_fst hA)).aemeasurable]
      refine lintegral_congr fun W => ?_
      by_cases hW : W ∈ A
      · simp only [Set.indicator, Set.mem_preimage, hW, if_true, Pi.one_apply, one_mul]
      · simp only [Set.indicator, Set.mem_preimage, hW, if_false, zero_mul, lintegral_zero]
    simp_rw [h1]
    have hm : ∀ Y : Finset (TorusSite n), Measurable fun W => A.indicator (1 : TorusField n → ENNReal) W *
        ∫⁻ ω, (if IsHullState R.params (clusterRange R.coupling) W Y
          then ENNReal.ofReal (R.labelWeight n W Y ω) else 0)
          ∂(Measure.pi fun _ : Y => R.labels.μ) :=
      fun Y => (measurable_one.indicator hA).mul (hd Y).lintegral_prod_right'
    rw [← lintegral_finsetSum _ fun Y _ => hm Y, ← lintegral_indicator hA]
    refine lintegral_congr fun W => ?_
    rw [← Finset.mul_sum, hsum]
    by_cases hW : W ∈ A <;> simp [Set.indicator, hW]
  have hfinW : IsFiniteMeasure ((fieldHaar n).withDensity fun W => ENNReal.ofReal (e W)) :=
    isFiniteMeasure_withDensity_ofReal hei.hasFiniteIntegral
  have hle : ∀ Y : Finset (TorusSite n), (stateMeasure R n Y).map Prod.fst ≤
      (fieldHaar n).withDensity fun W => ENNReal.ofReal (e W) := by
    intro Y
    rw [← hmeas]
    exact Measure.le_iff.mpr fun A _ => by
      rw [Measure.finsetSum_apply]
      exact Finset.single_le_sum (f := fun Y : Finset (TorusSite n) => ((stateMeasure R n Y).map Prod.fst) A)
        (fun _ _ => zero_le) (Finset.mem_univ Y)
  have hfin : ∀ Y, IsFiniteMeasure (stateMeasure R n Y) := by
    intro Y
    refine ⟨?_⟩
    have h1 := (hle Y) Set.univ
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h1
    exact lt_of_le_of_lt h1 (measure_lt_top _ _)
  refine ⟨hfin, fun F hF => ?_⟩
  have hFb : ∃ C : ℝ, ∀ W, ‖F W‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_range hF).isBounded.exists_norm_le
    exact ⟨C, fun W => hC _ ⟨W, rfl⟩⟩
  obtain ⟨C, hC⟩ := hFb
  have hint : IntegrableOnStates R n (fun W _ _ => F W) := fun Y => by
    have := hfin Y
    exact Integrable.of_bound (hF.measurable.comp measurable_fst).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC p.1)
  refine ⟨hint, ?_⟩
  have hFi : ∀ Y : Finset (TorusSite n), Integrable F ((stateMeasure R n Y).map Prod.fst) := by
    intro Y
    have := hfin Y
    have : IsFiniteMeasure ((stateMeasure R n Y).map Prod.fst) := inferInstance
    exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hstep : ∀ Y : Finset (TorusSite n), ∫ p : TorusField n × (Y → R.labels.Ω), F p.1 ∂(stateMeasure R n Y) =
      ∫ W, F W ∂((stateMeasure R n Y).map Prod.fst) := fun Y =>
    (integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable).symm
  have hem : Measurable fun W => ENNReal.ofReal (e W) := ENNReal.measurable_ofReal.comp hec.measurable
  unfold stateIntegralSum
  simp_rw [hstep]
  rw [← integral_finsetSum_measure fun Y _ => hFi Y, hmeas,
    integral_withDensity_eq_integral_toReal_smul hem
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_comm]
end Bottom
section Induction
variable {ℓ : StepParameters} (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam : ℝ) (x : ℕ → ℝ)
  (z₀ : StageWithResponse ℓ) (β : ℝ)
private def MomentIdentityAt (D : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n →
    (∀ Y, IsFiniteMeasure (stateMeasure (stageStep hL lam x z₀ s) n Y)) ∧
    stateIntegralSum (stageStep hL lam x z₀ s) n (fun _ _ _ => 1) ≠ 0 ∧
    ∀ {ι : Type} (I : Finset ι) (f : ι → StageWeight hL lam x z₀ s n), SeparatedAlong hL lam x z₀ I D s n f →
      IntegrableOnStates (stageStep hL lam x z₀ s) n (jointMoment hL lam x z₀ s n I f) ∧
      wilsonCenteredMoment hL lam x z₀ β s n I f * stateIntegralSum (stageStep hL lam x z₀ s) n (fun _ _ _ => 1) =
        stateIntegralSum (stageStep hL lam x z₀ s) n (jointMoment hL lam x z₀ s n I f)
private def StepTransferProperty (R : StepSetup) (h : CoarseLabelFacts R) (lam x'' : ℝ) : Prop :=
  ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
    (∀ Yt : Finset (TorusSite (n * R.params.side)), IsFiniteMeasure (stateMeasure R (n * R.params.side) Yt)) →
    (∀ Y : Finset (TorusSite n), IsFiniteMeasure (stateMeasure (nextStepSetup R h lam x'') n Y)) ∧
    stateIntegralSum (nextStepSetup R h lam x'') n (fun _ _ _ => 1) =
      stateIntegralSum R (n * R.params.side) (fun _ _ _ => 1) ∧
    StepMeanProperty R h lam x'' n
private theorem momentIdentityAt_succ (hT : BondScoreProperties) (hS : ScoreProductStepMean) (hfit : ℓ.Admissible)
    (D : ℕ → ℕ) (s : ℕ)
    (hF : StepTransferProperty (stageStep hL lam x z₀ s) (hL (stagesFrom hL lam x z₀ s).1) lam (x (s + 2)))
    (ih : MomentIdentityAt hL lam x z₀ β D s) : MomentIdentityAt hL lam x z₀ β D (s + 1) := by
  classical
  intro n _ hb
  have hL0 : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : ℓ.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hL0) hb.2
  have hb' : IsBlockTorusSide ℓ (n * ℓ.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  obtain ⟨hfin, hZ, hall⟩ := ih (n * ℓ.side) hb'
  obtain ⟨hfa, hZe, hM⟩ := hF n hb hfin
  refine ⟨hfa, ?_, ?_⟩
  · exact fun h0 => hZ (hZe.symm.trans h0)
  · intro ι I f hA
    obtain ⟨h1, h2, h3, h4⟩ := hA
    have hsep := bondCoefficient_disjoint_of_far (n := n) (stageResponse hL lam x z₀ s) I f (D s) h3 h4
    have hG : ∀ J ∈ I.powerset, IntegrableOnStates (stageStep hL lam x z₀ s) (n * ℓ.side)
        (jointMoment hL lam x z₀ s (n * ℓ.side) J f) := fun J hJ =>
      (hall J f (separatedAlong_mono hL lam x z₀ (Finset.mem_powerset.mp hJ) D s (n * ℓ.side) f h1)).1
    have hs := stepJointMoment_integrable_and_eq (stageResponse hL lam x z₀ s) hT hS hfit hM I f hsep
      (fun J => jointMoment hL lam x z₀ s (n * ℓ.side) J f) hG
    have hmom : jointMoment hL lam x z₀ (s + 1) n I f =
        stepJointMoment (stageResponse hL lam x z₀ s) I f
          (fun J => jointMoment hL lam x z₀ s (n * ℓ.side) J f) := by
      funext V Y ω
      rfl
    refine ⟨?_, ?_⟩
    · rw [hmom]
      exact hs.1
    · have key : ∀ Za : ℝ, Za = stateIntegralSum (stageStep hL lam x z₀ s) (n * ℓ.side) (fun _ _ _ => 1) →
          wilsonCenteredMoment hL lam x z₀ β (s + 1) n I f * Za = ∑ J ∈ I.powerset,
            (∏ i ∈ I \ J, -stepMeanShift (stageResponse hL lam x z₀ s) (f i)) *
              stateIntegralSum (stageStep hL lam x z₀ s) (n * ℓ.side)
                (jointMoment hL lam x z₀ s (n * ℓ.side) J f) := by
        intro Za hZa
        rw [hZa, wilsonCenteredMoment_succ, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [mul_assoc, (hall J f (separatedAlong_mono hL lam x z₀ (Finset.mem_powerset.mp hJ) D s
          (n * ℓ.side) f h1)).2]
      rw [hmom]
      exact (key _ hZe).trans hs.2.symm
end Induction
section First
private theorem momentIdentityAt_zero (T : ParameterAssignment) (y β : ℝ) (K : ResponseParameters) (f₀ : LocalDensity)
    (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup) (lam : ℝ) (x : ℕ → ℝ)
    (D : ℕ → ℕ)
    (hrow : (stageStep hL lam x (initialStage T y β K f₀ Λ Dq Φ φ) 0).HasExpansions) :
    MomentIdentityAt hL lam x (initialStage T y β K f₀ Λ Dq Φ φ) β D 0 := by
  classical
  intro n _ hb
  obtain ⟨hfin, hmean⟩ := stateIntegralSum_of_wilsonWeight hrow hb (β := β) rfl
  set e : TorusField n → ℝ := fun W => Real.exp (-β * wilsonAction Finset.univ W) with he
  have hec : Continuous e := continuous_wilsonBoltzmann β
  have hei : Integrable e (fieldHaar n) :=
    hec.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ : stateIntegralSum (stageStep hL lam x (initialStage T y β K f₀ Λ Dq Φ φ) 0) n (fun _ _ _ => 1) =
      ∫ W, e W ∂(fieldHaar n) := by
    refine (hmean (fun _ => 1) continuous_const).2.trans ?_
    simp only [one_mul]
    rfl
  have hpos : 0 < ∫ W, e W ∂(fieldHaar n) := integral_exp_pos hei
  refine ⟨hfin, by rw [hZ]; exact hpos.ne', fun I f hA => ?_⟩
  have hG : jointMoment hL lam x (initialStage T y β K f₀ Λ Dq Φ φ) 0 n I f =
      fun W _ _ => ∏ i ∈ I, curvatureObservable (m := n) (f i) W := by
    funext W Y ω
    refine Finset.prod_congr rfl fun i _ => ?_
    exact sum_support_siteResponse_sub (T.stepParameters y).side (f i) W
  have hFc : Continuous fun W : TorusField n => ∏ i ∈ I, curvatureObservable (m := n) (f i) W :=
    continuous_finsetProd _ fun i _ => curvatureObservable_continuous _
  obtain ⟨hi, hv⟩ := hmean _ hFc
  rw [hG]
  refine ⟨hi, ?_⟩
  rw [hv, hZ]
  have hdm : Measurable fun W : TorusField n => ENNReal.ofReal (e W / ∫ W', e W' ∂(fieldHaar n)) :=
    ENNReal.measurable_ofReal.comp (hec.measurable.div_const _)
  have hw : wilsonCenteredMoment hL lam x (initialStage T y β K f₀ Λ Dq Φ φ) β 0 n I f =
      ∫ W, (e W / ∫ W', e W' ∂(fieldHaar n)) * ∏ i ∈ I, curvatureObservable (m := n) (f i) W ∂(fieldHaar n) := by
    have h0 : wilsonCenteredMoment hL lam x (initialStage T y β K f₀ Λ Dq Φ φ) β 0 n I f =
        ∫ W, ∏ i ∈ I, curvatureObservable (m := n) (f i) W ∂(wilsonLaw β n) := by
      unfold wilsonCenteredMoment
      refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
      refine Finset.prod_congr rfl fun i _ => ?_
      show _ - (0 : ℝ) = _
      exact sub_zero _
    rw [h0]
    unfold wilsonLaw
    rw [integral_withDensity_eq_integral_toReal_smul hdm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hpos.le)]
  rw [hw]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, div_mul_cancel₀ _ hpos.ne']
  exact integral_congr_ae (Filter.Eventually.of_forall fun W => mul_comm _ _)
end First
end MomentsAlongStages
open MomentsAlongStages in
theorem momentsAlongStagesStatement_holds (hM : stepMeanOfStatesStatement) (hS : ScoreProductStepMean)
    (hT : BondScoreProperties) (hF : StagesAreWellPosed) : momentsAlongStagesStatement := by
  refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
  intro T hD _ K
  obtain ⟨y₁, h1⟩ := hM T hD
  obtain ⟨y₂, h2⟩ := hF T hD
  refine ⟨max y₁ y₂, ?_⟩
  intro y β hL z₀ hy hfirst s hst n _ hb ι I D f hA
  have hy1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : y₂ ≤ y := le_trans (le_max_right _ _) hy
  have hform := h2 y hy2 K β hL z₀ hfirst s hst
  have hfit : (T.stepParameters y).Admissible := (hform 0 (Nat.zero_le _)).admissible
  have hall : ∀ t ≤ s, MomentIdentityAt hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ β D t := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨K', f₀, Λ, Dq, Φ, φ, rfl⟩ := hfirst.isWilson
      exact momentIdentityAt_zero T y β K' f₀ Λ Dq Φ φ hL _ _ D (hform 0 (Nat.zero_le _)).hasExpansions
    | succ t ih =>
      intro ht
      refine momentIdentityAt_succ hL T.lam _ z₀ β hT hS hfit D t ?_ (ih (by omega))
      intro m _ hbm hfm
      obtain ⟨e1, e2, e3⟩ := h1 y hy1 _ (hst t (by omega)).onFamily.onFamily (hform t (by omega))
        (hL (stagesFrom hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t).1) T.lam
        (couplingsAlongFlow (T.stepParameters y) β (t + 2)) m hbm hfm
      exact ⟨e1, e2, e3⟩
  obtain ⟨hfin, hZ, hmom⟩ := hall s le_rfl n hb
  obtain ⟨hi, he⟩ := hmom I f hA
  have hrow := (hform s le_rfl).hasExpansions
  have hone : IntegrableOnStates (stageStep hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s) n
      (fun _ _ _ => 1) := fun Y => by
    have := hfin Y
    exact integrable_const _
  rw [stateIntegral_eq_stateIntegralSum hrow hb _ hi, stateIntegral_eq_stateIntegralSum hrow hb _ hone,
    eq_div_iff hZ]
  exact he
end YangMills.Construction.ResponseInTheExpansion
end
