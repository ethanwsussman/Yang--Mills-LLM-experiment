import YangMills.Construction.FreeEnergiesOfTheFlow.MeanOfTheVariableOfAStepProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansOfPositiveFunctionsOverTheCases
import YangMills.Construction.ResponseInTheExpansion.MeansGivenAStateAreMeansOverItsCases
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import YangMills.Construction.ResponseInTheExpansion.TwoPointFunctionByTotalCovariance
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction.FreeEnergies
open TorusFields TorusLumps StepSettings StepCosts WeightedResponses
private theorem cutoffFactor_mem_unit {r : ℝ} {c : ℝ → ℝ} (hc : ColdStepAtMirrorFrames.IsCutoff r c) {t : ℝ}
    (ht : 0 ≤ t) :
    0 ≤ ColdStepAtMirrorFrames.cutoffFactor r c t ∧ ColdStepAtMirrorFrames.cutoffFactor r c t ≤ 1 := by apply _root_.YangMills.SharedProofs.p2957 <;> assumption
section Weight
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markProduct_nonneg (hc : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn)
    (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side))) : 0 ≤ markProduct R C V W bad := by
  unfold markProduct
  refine Finset.prod_nonneg fun e _ => ?_
  have h : 0 ≤ bondMark R V W e ∧ bondMark R V W e ≤ 1 := cutoffFactor_mem_unit hc (norm_nonneg _)
  split_ifs <;> linarith [h.1, h.2]
private theorem baseLaw_mul_prod_bondKernel (V : TorusField n) (W : TorusField (n * R.params.side))
    (b : BaseChoice R.params.side n) :
    baseLaw (R := R) W b * (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) =
      stepTransitionDensity R.params R.coupling W b V := by
  classical
  unfold baseLaw stepTransitionDensity
  split_ifs <;> simp
private theorem stepWeight_nonneg (hS : StepTransitionDensityBounds) (hexp : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hc : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn) (C : Finset (TorusSite n))
    (V : TorusField n) (W : TorusField (n * R.params.side)) (Y : Finset (TorusSite (n * R.params.side)))
    (ω : Y → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hY : IsHullState R.params R.range W Y) :
    0 ≤ stepWeight R C V W Y ω bad b := by
  have : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne R.params.side)⟩
  have hD : 0 ≤ R.labelWeight (n * R.params.side) W Y ω :=
    hexp.2.nonneg (n * R.params.side) hside W Y ω hY
  obtain ⟨-, K, hK⟩ := hS R.params R.coupling n
  have hd := (hK W b V).1
  rw [← baseLaw_mul_prod_bondKernel (R := R)] at hd
  unfold stepWeight
  rw [mul_assoc (R.labelWeight (n * R.params.side) W Y ω)]
  exact mul_nonneg (mul_nonneg hD hd) (markProduct_nonneg hc C V W bad)
private def truncate (F : CaseFunction R n) (N : ℕ) : CaseFunction R n :=
  fun W Y ω bad b => min (F W Y ω bad b) (N : ℝ)
private theorem caseTerm_truncate (hS : StepTransitionDensityBounds) (hexp : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hc : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn) (C : Finset (TorusSite n))
    (V : TorusField n) (q : CoarseState R n) (F : CaseFunction R n) (N : ℕ)
    (bad : Finset (TorusBond (n * R.params.side))) (Y : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ν : q.unlabelled Y → R.labels.Ω) :
    caseTerm R C V q (truncate F N) bad Y b W ν =
      min (caseTerm R C V q F bad Y b W ν) ((N : ℝ) * caseTerm R C V q (fun _ _ _ _ _ => 1) bad Y b W ν) := by
  unfold caseTerm truncate
  split_ifs with h
  · rw [one_mul, min_mul_of_nonneg _ _ (stepWeight_nonneg hS hexp hside hc C V _ Y _ bad b h.1)]
  · simp
private theorem tendsto_min_natCast (a : ℝ) : Tendsto (fun N : ℕ => min a (N : ℝ)) atTop (𝓝 a) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈a⌉₊] with N hN
  exact (min_eq_left ((Nat.le_ceil a).trans (by exact_mod_cast hN))).symm
private theorem tendsto_caseMean_truncate (hS : StepTransitionDensityBounds) (hexp : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hc : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn) (C : Finset (TorusSite n))
    (V : TorusField n) (q : CoarseState R n) (F : CaseFunction R n) (hF0 : ∀ W Y ω bad b, 0 ≤ F W Y ω bad b)
    (hF : CaseIntegrable R C V q F) (hone : CaseIntegrable R C V q fun _ _ _ _ _ => 1) :
    Tendsto (fun N : ℕ => caseMean R C V q (truncate F N)) atTop (𝓝 (caseMean R C V q F)) := by
  have htr : ∀ (N : ℕ) bad, bad ∈ (markedBonds R C).powerset → ∀ Y b,
      Integrable (fun z : TorusField (n * R.params.side) × (q.unlabelled Y → R.labels.Ω) =>
        caseTerm R C V q (truncate F N) bad Y b z.1 z.2)
      ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := by
    intro N bad hbad Y b
    have e : (fun z : TorusField (n * R.params.side) × (q.unlabelled Y → R.labels.Ω) =>
        caseTerm R C V q (truncate F N) bad Y b z.1 z.2) =
        (fun z : TorusField (n * R.params.side) × (q.unlabelled Y → R.labels.Ω) =>
          caseTerm R C V q F bad Y b z.1 z.2) ⊓
        (fun z : TorusField (n * R.params.side) × (q.unlabelled Y → R.labels.Ω) =>
          (N : ℝ) * caseTerm R C V q (fun _ _ _ _ _ => 1) bad Y b z.1 z.2) := by
      funext z
      exact caseTerm_truncate hS hexp hside hc C V q F N bad Y b z.1 z.2
    rw [e]
    exact (hF bad hbad Y b).inf ((hone bad hbad Y b).const_mul _)
  unfold caseMean caseIntegral
  refine Tendsto.div_const ?_ _
  refine tendsto_finsetSum _ fun bad hbad => tendsto_finsetSum _ fun Y _ => tendsto_finsetSum _ fun b _ => ?_
  have e1 : ∀ N : ℕ, ∫ W, ∫ ν : q.unlabelled Y → R.labels.Ω, caseTerm R C V q (truncate F N) bad Y b W ν
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫ z : TorusField (n * R.params.side) × (q.unlabelled Y → R.labels.Ω),
        caseTerm R C V q (truncate F N) bad Y b z.1 z.2
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := fun N =>
    (integral_prod _ (htr N bad hbad Y b)).symm
  have e2 : ∫ W, ∫ ν : q.unlabelled Y → R.labels.Ω, caseTerm R C V q F bad Y b W ν
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫ z : TorusField (n * R.params.side) × (q.unlabelled Y → R.labels.Ω), caseTerm R C V q F bad Y b z.1 z.2
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) :=
    (integral_prod _ (hF bad hbad Y b)).symm
  simp only [e1, e2]
  refine tendsto_integral_of_dominated_convergence
    (fun z => |caseTerm R C V q F bad Y b z.1 z.2|) (fun N => (htr N bad hbad Y b).aestronglyMeasurable)
    (hF bad hbad Y b).abs (fun N => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · unfold caseTerm truncate
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have ha := hF0 (q.fieldWithStoredLinks z.1) Y (q.fillLabels Y z.2) bad b
      rw [abs_of_nonneg (le_min ha (Nat.cast_nonneg N)), abs_of_nonneg ha]
      exact min_le_left _ _
    · simp
  · unfold caseTerm truncate
    split_ifs
    · exact (tendsto_min_natCast _).mul_const _
    · exact tendsto_const_nhds
end Weight
private theorem lintegral_eq_caseMean_of_nonneg {ℓ : TorusLumps.StepParameters} {T : StageTower ℓ} {β : ℝ}
    {s n : ℕ} [NeZero n] (hS : StepTransitionDensityBounds)
    (hprob : IsProbabilityMeasure (markedSampleLaw T β (s + 1) n))
    (hle : stageSigma T (s + 1) n ≤ markedSampleMeasurableSpace ℓ (s + 1) n)
    (hexp : (T.stage s).toStepSetup.HasExpansions) (hside : IsBlockTorusSide ℓ (n * ℓ.side))
    (hc : ColdStepAtMirrorFrames.IsCutoff (T.stage s).toStepSetup.ballRadius (T.stage s).toStepSetup.barrierFn)
    (hMG : ∀ F : TorusField n → CaseFunction (T.stage s).toStepSetup n,
      (Measurable fun u : MarkedSample ℓ (s + 1) n => F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
        (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1) →
      (∃ C : ℝ, ∀ u : MarkedSample ℓ (s + 1) n, |F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
        (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1| ≤ C) →
      ((markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n =>
          F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
          (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1 |
          stageSigma T (s + 1) n]) =ᵐ[markedSampleLaw T β (s + 1) n]
        fun u => caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
          (stageState T (s + 1) n u).2 (F u.2.2.1))
    (F : TorusField n → CaseFunction (T.stage s).toStepSetup n) (hF0 : ∀ V W Y ω bad b, 0 ≤ F V W Y ω bad b)
    (hm : Measurable fun u : MarkedSample ℓ (s + 1) n => F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
      (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1)
    (hint : ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n),
      CaseIntegrable (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 (F u.2.2.1) ∧
      CaseIntegrable (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 fun _ _ _ _ _ => 1) :
    AEMeasurable (fun u => caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
      (stageState T (s + 1) n u).2 (F u.2.2.1)) (markedSampleLaw T β (s + 1) n) ∧
    ∫⁻ u, ENNReal.ofReal (F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
        (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1)
        ∂(markedSampleLaw T β (s + 1) n) =
      ∫⁻ u, ENNReal.ofReal (caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1)
        u.2.2.1 (stageState T (s + 1) n u).2 (F u.2.2.1)) ∂(markedSampleLaw T β (s + 1) n) := by
  set μ := markedSampleLaw T β (s + 1) n with hμ
  set f : MarkedSample ℓ (s + 1) n → ℝ := fun u => F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
    (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1 with hf
  let FN : ℕ → TorusField n → CaseFunction (T.stage s).toStepSetup n := fun N V => truncate (F V) N
  let fN : ℕ → MarkedSample ℓ (s + 1) n → ℝ := fun N u => min (f u) (N : ℝ)
  let g : ℕ → MarkedSample ℓ (s + 1) n → ℝ := fun N u =>
    caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
      (stageState T (s + 1) n u).2 (FN N u.2.2.1)
  have hmN : ∀ N, Measurable (fN N) := fun N => hm.min measurable_const
  have hbN : ∀ N u, |fN N u| ≤ (N : ℝ) := fun N u => by
    have ha : 0 ≤ f u := hF0 _ _ _ _ _ _
    rw [abs_of_nonneg (le_min ha (Nat.cast_nonneg N))]
    exact min_le_right _ _
  have hiN : ∀ N, Integrable (fN N) μ := fun N =>
    Integrable.of_bound (hmN N).aestronglyMeasurable (N : ℝ)
      (Eventually.of_forall fun u => by simpa using hbN N u)
  have hce : ∀ N, μ[fN N | stageSigma T (s + 1) n] =ᵐ[μ] g N := fun N =>
    hMG (FN N) (hmN N) ⟨(N : ℝ), hbN N⟩
  have hig : ∀ N, Integrable (g N) μ := fun N =>
    (integrable_condExp (m := stageSigma T (s + 1) n) (μ := μ) (f := fN N)).congr (hce N)
  have hfN0 : ∀ N, 0 ≤ᵐ[μ] fN N := fun N => Eventually.of_forall fun u =>
    le_min (hF0 _ _ _ _ _ _) (Nat.cast_nonneg N)
  have hg0 : ∀ N, 0 ≤ᵐ[μ] g N := fun N => by
    filter_upwards [hce N, condExp_nonneg (m := stageSigma T (s + 1) n) (hfN0 N)] with u h1 h2
    rw [← h1]
    exact h2
  have hmean : ∀ N, ∫⁻ u, ENNReal.ofReal (fN N u) ∂μ = ∫⁻ u, ENNReal.ofReal (g N u) ∂μ := fun N => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hiN N) (hfN0 N),
      ← ofReal_integral_eq_lintegral_ofReal (hig N) (hg0 N),
      ← integral_congr_ae (hce N), integral_condExp hle]
  have hmono : ∀ᵐ u ∂μ, Monotone fun N => g N u := by
    have : ∀ N, ∀ᵐ u ∂μ, g N u ≤ g (N + 1) u := fun N => by
      have hf_le : fN N ≤ᵐ[μ] fN (N + 1) := Eventually.of_forall fun u =>
        min_le_min_left _ (by exact_mod_cast Nat.le_succ N)
      filter_upwards [condExp_mono (m := stageSigma T (s + 1) n) (hiN N) (hiN (N + 1)) hf_le, hce N,
        hce (N + 1)] with u h1 h2 h3
      rw [← h2, ← h3]
      exact h1
    filter_upwards [ae_all_iff.2 this] with u hu
    exact monotone_nat_of_le_succ hu
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun N => g N u) atTop
      (𝓝 (caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 (F u.2.2.1))) := by
    filter_upwards [hint] with u hu
    exact tendsto_caseMean_truncate hS hexp hside hc _ _ _ _ (hF0 u.2.2.1) hu.1 hu.2
  have hL := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (f := fun N u => ENNReal.ofReal (fN N u)) (F := fun u => ENNReal.ofReal (f u))
    (fun N => (hmN N).ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun u => fun a b hab => ENNReal.ofReal_le_ofReal
      (min_le_min_left _ (by exact_mod_cast hab)))
    (Eventually.of_forall fun u => (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_min_natCast _))
  have hR := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (f := fun N u => ENNReal.ofReal (g N u))
    (F := fun u => ENNReal.ofReal (caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1)
        u.2.2.1 (stageState T (s + 1) n u).2 (F u.2.2.1)))
    (fun N => (hig N).aemeasurable.ennreal_ofReal)
    (by
      filter_upwards [hmono] with u hu a b hab
      exact ENNReal.ofReal_le_ofReal (hu hab))
    (by
      filter_upwards [hlim] with u hu
      exact (ENNReal.continuous_ofReal.tendsto _).comp hu)
  simp only [hmean] at hL
  exact ⟨aemeasurable_of_tendsto_metrizable_ae atTop (fun N => (hig N).aemeasurable) hlim,
    tendsto_nhds_unique hL hR⟩
theorem caseMeanTowerStatement_holds (hMG : ResponseInTheExpansion.conditionalMeanIsCaseMeanStatement)
    (hTP : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hS : StepTransitionDensityBounds) :
    caseMeanTowerStatement := by
  intro a ha
  obtain ⟨L₀, r₀, hr₀, h⟩ := hMG a ha
  refine ⟨L₀, r₀, hr₀, fun L hodd hL Tb hTa hTL hD hr => ?_⟩
  obtain ⟨y₀, hy⟩ := h L hodd hL Tb hTa hTL hD hr
  refine ⟨y₀, fun y hyy hret hw T β s n _ hst hcut hcoin hF hside hd F hF0 hm hint => ?_⟩
  obtain ⟨hprob, hle, -⟩ := hTP _ hF.admissible hF.admissible.depth_lt T hcut hcoin β (fun _ => 0) (s + 1) n
  exact lintegral_eq_caseMean_of_nonneg hS hprob hle hF.hasExpansions hside hF.isCutoff
    (fun F hm' hb' => hy y hyy hret hw T β s n hst hcut hcoin hF hside hd F hm' hb') F hF0 hm hint
end YangMills.Construction.FreeEnergies
end
