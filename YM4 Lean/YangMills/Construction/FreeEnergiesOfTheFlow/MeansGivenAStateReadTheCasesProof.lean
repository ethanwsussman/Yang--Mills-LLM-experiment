import YangMills.Construction.FreeEnergiesOfTheFlow.MeanOfTheVariableOfAStepProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansGivenAStateReadTheCases
import YangMills.Construction.ResponseInTheExpansion.MeansGivenAStateAreMeansOverItsCases
import YangMills.Construction.ResponseInTheExpansion.TwoPointFunctionByTotalCovariance
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace YangMills.Construction.FreeEnergies
open TorusLumps WeightedResponses StepSettings TorusFields StepCosts ColdStepAtMirrorFrames BlockAverages
section Cases
variable {ℓ : TorusLumps.StepParameters} {T : WeightedResponses.StageTower ℓ} {β : ℝ}
private theorem abs_clip_le (k a : ℝ) (hk : 0 ≤ k) : |max (-k) (min k a)| ≤ k := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
private theorem clip_eq_self {k a : ℝ} (h : |a| ≤ k) : max (-k) (min k a) = a := by
  have hab := abs_le.1 h
  rw [min_eq_right hab.2, max_eq_right hab.1]
abbrev _root_.YangMills.DeltaSharedProofs.p15858 := @clip_eq_self
private theorem condExp_eq_caseMean_of_ae_bounded (hC : caseMeanProperties)
    (s n : ℕ) [NeZero n]
    (hMG : ∀ F : TorusField n → WeightedResponses.CaseFunction (T.stage s).toStepSetup n, Measurable (caseLift T s n F) → (∃ C : ℝ, ∀ x, |caseLift T s n F x| ≤ C) →
      (markedSampleLaw T β (s + 1) n)[caseLift T s n F | stageSigma T (s + 1) n] =ᵐ[markedSampleLaw T β (s + 1) n] caseMeanAtSample T s n F)
    (hw : ∀ (C : Finset (TorusSite n)) (V : TorusField n) W Yt ωt bad b, 0 ≤ StepSettings.stepWeight (T.stage s).toStepSetup C V W Yt ωt bad b)
    (hone : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), CaseIntegrableAtSample T s n (fun _ _ _ _ _ _ => 1) x)
    {F : TorusField n → WeightedResponses.CaseFunction (T.stage s).toStepSetup n} (hm : Measurable (caseLift T s n F)) {K : ℝ}
    (hK : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), |caseLift T s n F x| ≤ K)
    (hI : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), CaseIntegrableAtSample T s n F x) :
    (markedSampleLaw T β (s + 1) n)[caseLift T s n F | stageSigma T (s + 1) n] =ᵐ[markedSampleLaw T β (s + 1) n] caseMeanAtSample T s n F := by
  have htrunc : ∀ k : ℕ, K ≤ k → ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n),
      ((markedSampleLaw T β (s + 1) n)[caseLift T s n F | stageSigma T (s + 1) n]) x =
        caseMeanAtSample T s n (fun V => truncateCases (k : ℝ) (F V)) x := by
    intro k hk
    have hlift : ∀ x, caseLift T s n (fun V => truncateCases (k : ℝ) (F V)) x = max (-(k : ℝ)) (min (k : ℝ) (caseLift T s n F x)) :=
      fun _ => rfl
    have hmk : Measurable (caseLift T s n (fun V => truncateCases (k : ℝ) (F V))) := by
      have heq : caseLift T s n (fun V => truncateCases (k : ℝ) (F V)) = fun x => max (-(k : ℝ)) (min (k : ℝ) (caseLift T s n F x)) :=
        funext hlift
      rw [heq]
      exact measurable_const.max (measurable_const.min hm)
    have hbd : ∃ C : ℝ, ∀ x, |caseLift T s n (fun V => truncateCases (k : ℝ) (F V)) x| ≤ C :=
      ⟨k, fun x => by rw [hlift]; exact abs_clip_le _ _ (Nat.cast_nonneg k)⟩
    have hae : caseLift T s n F =ᵐ[markedSampleLaw T β (s + 1) n] caseLift T s n (fun V => truncateCases (k : ℝ) (F V)) := by
      filter_upwards [hK] with x hx
      rw [hlift, clip_eq_self (hx.trans hk)]
    exact (condExp_congr_ae hae).trans (hMG _ hmk hbd)
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge K
  have hall : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), ∀ k : ℕ, k₀ ≤ k →
      ((markedSampleLaw T β (s + 1) n)[caseLift T s n F | stageSigma T (s + 1) n]) x =
        caseMeanAtSample T s n (fun V => truncateCases (k : ℝ) (F V)) x := by
    rw [ae_all_iff]
    intro k
    by_cases hk : k₀ ≤ k
    · filter_upwards [htrunc k (hk₀.trans (Nat.cast_le.2 hk))] with x hx _ using hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hk
  filter_upwards [hall, hone, hI] with x hx hx1 hxI
  have hlim := ((hC (T.stage s).toStepSetup n (hotCoreSites (T.stage s).toStepSetup x.2.2.1) x.2.2.1 (stageState T (s + 1) n x).2
    (fun W Yt ωt bad b _ => hw _ _ W Yt ωt bad b)).2.2.2.2.2 hx1 (F x.2.2.1) hxI).2
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
  exact hx k hk
private theorem abs_condExp_le_caseMean (hC : caseMeanProperties) (s n : ℕ) [NeZero n] [IsFiniteMeasure (markedSampleLaw T β (s + 1) n)]
    (hMG : ∀ F : TorusField n → WeightedResponses.CaseFunction (T.stage s).toStepSetup n, Measurable (caseLift T s n F) → (∃ C : ℝ, ∀ x, |caseLift T s n F x| ≤ C) →
      (markedSampleLaw T β (s + 1) n)[caseLift T s n F | stageSigma T (s + 1) n] =ᵐ[markedSampleLaw T β (s + 1) n] caseMeanAtSample T s n F)
    (hw : ∀ (C : Finset (TorusSite n)) (V : TorusField n) W Yt ωt bad b, 0 ≤ StepSettings.stepWeight (T.stage s).toStepSetup C V W Yt ωt bad b)
    (hone : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), CaseIntegrableAtSample T s n (fun _ _ _ _ _ _ => 1) x)
    {φ : TorusField n → WeightedResponses.CaseFunction (T.stage s).toStepSetup n} (hφ : ∀ V W Yt ωt bad b, 0 ≤ φ V W Yt ωt bad b)
    (hm : Measurable (caseLift T s n φ)) (hI : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), CaseIntegrableAtSample T s n φ x)
    {D : MarkedSample ℓ (s + 1) n → ℝ} (hD : Integrable D (markedSampleLaw T β (s + 1) n)) {K : ℝ}
    (hK : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), |D x| ≤ K)
    (hle : ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), |D x| ≤ caseLift T s n φ x) :
    ∀ᵐ x ∂(markedSampleLaw T β (s + 1) n), |((markedSampleLaw T β (s + 1) n)[D | stageSigma T (s + 1) n]) x| ≤ caseMeanAtSample T s n φ x := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hlift : ∀ x, caseLift T s n (fun V => truncateCases (k : ℝ) (φ V)) x = max (-(k : ℝ)) (min (k : ℝ) (caseLift T s n φ x)) :=
    fun _ => rfl
  have hmk : Measurable (caseLift T s n (fun V => truncateCases (k : ℝ) (φ V))) := by
    have heq : caseLift T s n (fun V => truncateCases (k : ℝ) (φ V)) = fun x => max (-(k : ℝ)) (min (k : ℝ) (caseLift T s n φ x)) :=
      funext hlift
    rw [heq]
    exact measurable_const.max (measurable_const.min hm)
  have hbd : ∀ x, |caseLift T s n (fun V => truncateCases (k : ℝ) (φ V)) x| ≤ k :=
    fun x => by rw [hlift]; exact abs_clip_le _ _ (Nat.cast_nonneg k)
  have hkI : Integrable (caseLift T s n (fun V => truncateCases (k : ℝ) (φ V))) (markedSampleLaw T β (s + 1) n) :=
    Integrable.of_bound hmk.aestronglyMeasurable k (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hbd x)
  have hDle : (fun x => |D x|) ≤ᵐ[markedSampleLaw T β (s + 1) n] caseLift T s n (fun V => truncateCases (k : ℝ) (φ V)) := by
    filter_upwards [hK, hle] with x hxK hxφ
    rw [hlift]
    exact le_max_of_le_right (le_min (hxK.trans hk) hxφ)
  have habs := abs_condExp_ae_le_condExp_abs (μ := markedSampleLaw T β (s + 1) n) (m := stageSigma T (s + 1) n) D
  have hmono' := condExp_mono (m := stageSigma T (s + 1) n) hD.abs hkI hDle
  have hcase := hMG _ hmk ⟨k, hbd⟩
  filter_upwards [habs, hmono', hcase, hone, hI] with x hxa hxm hxc hx1 hxI
  have hprops := hC (T.stage s).toStepSetup n (hotCoreSites (T.stage s).toStepSetup x.2.2.1) x.2.2.1 (stageState T (s + 1) n x).2 (fun W Yt ωt bad b _ => hw _ _ W Yt ωt bad b)
  have htruncI := (hprops.2.2.2.2.2 hx1 (φ x.2.2.1) hxI).1 k (Nat.cast_nonneg k)
  have hmono := hprops.2.2.2.1 _ _ htruncI hxI (fun W Yt ωt bad b _ _ => by
    show max (-(k : ℝ)) (min (k : ℝ) (φ x.2.2.1 W Yt ωt bad b)) ≤ φ x.2.2.1 W Yt ωt bad b
    have hnn := hφ x.2.2.1 W Yt ωt bad b
    exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) (min_le_right _ _))
  calc |((markedSampleLaw T β (s + 1) n)[D | stageSigma T (s + 1) n]) x|
      ≤ ((markedSampleLaw T β (s + 1) n)[fun x => |D x| | stageSigma T (s + 1) n]) x := hxa
    _ ≤ ((markedSampleLaw T β (s + 1) n)[caseLift T s n (fun V => truncateCases (k : ℝ) (φ V)) | stageSigma T (s + 1) n]) x := hxm
    _ = caseMeanAtSample T s n (fun V => truncateCases (k : ℝ) (φ V)) x := hxc
    _ ≤ caseMeanAtSample T s n φ x := hmono
end Cases
section Weight
variable {ℓ : TorusLumps.StepParameters}
private theorem cutoffFactor_mem_unit {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ cutoffFactor ρ p u ∧ cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.SharedProofs.p2957 <;> assumption
private theorem stage_barrierFn (T : WeightedResponses.StageTower ℓ) : ∀ t, (T.stage t).barrierFn = T.base.barrierFn
  | 0 => rfl
  | t + 1 => stage_barrierFn T t
private theorem stage_isCutoff (T : WeightedResponses.StageTower ℓ) (h : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by
  show IsCutoff (ℓ.threshold / 64) (T.stage t).barrierFn
  rw [stage_barrierFn]
  exact h
abbrev _root_.YangMills.SharedProofs.p16 := @stage_isCutoff
private theorem labelWeight_nonneg {T : WeightedResponses.StageTower ℓ} {β : ℝ} (hs : ResponseInTheExpansion.StageTower.StartsAtWilson T β) (u n : ℕ) [NeZero n] (W : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → (T.stage u).labels.Ω) : 0 ≤ (T.stage u).labelWeight n W Y ω := by
  cases u with
  | zero =>
    have h := hs.labelWeight_eq n W Y ω
    have h' : (T.stage 0).labelWeight n W Y ω = T.base.labelWeight n W Y ω := rfl
    rw [h', h]
    split_ifs
    · show 0 ≤ wilsonWeight β n W
      unfold wilsonWeight
      rw [dif_neg (NeZero.ne n)]
      exact (Real.exp_pos _).le
    · exact le_rfl
  | succ s =>
    show 0 ≤ coarseWeightExpansion (T.stage s).toStepSetup n W Y ω
    unfold coarseWeightExpansion
    rw [dif_neg (NeZero.ne n)]
    exact ENNReal.toReal_nonneg
private theorem stepWeight_nonneg (hK : BondKernelProperties) {T : WeightedResponses.StageTower ℓ} {β : ℝ} (hs : ResponseInTheExpansion.StageTower.StartsAtWilson T β)
    (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (u n : ℕ) [NeZero n] (C : Finset (TorusSite n)) (V : TorusField n) W Yt ωt bad b :
    0 ≤ StepSettings.stepWeight (T.stage u).toStepSetup C V W Yt ωt bad b := by
  classical
  unfold StepSettings.stepWeight
  refine mul_nonneg (mul_nonneg (mul_nonneg (labelWeight_nonneg hs u _ W Yt ωt) ?_) ?_) ?_
  · unfold baseLaw
    split_ifs
    · positivity
    · exact le_rfl
  · exact Finset.prod_nonneg fun c _ => (hK.2 _ _ _ _ _ _ _).1.le
  · unfold markProduct
    refine Finset.prod_nonneg fun β' _ => ?_
    have h := cutoffFactor_mem_unit (stage_isCutoff T hcut u) (u := ‖((chartCoord (T.stage u).toStepSetup.params V W β' : imaginaryQuaternions) : Quaternion ℝ) -
        ((frameCoord (T.stage u).toStepSetup.params (T.stage u).toStepSetup.anchorRadius (T.stage u).toStepSetup.depth (T.stage u).toStepSetup.frameReach V β' : imaginaryQuaternions) : Quaternion ℝ)‖) (norm_nonneg _)
    split_ifs
    · unfold bondMark
      linarith [h.2]
    · exact h.1
end Weight
theorem conditionalMeanReadsCases_proof (hG : ResponseInTheExpansion.conditionalMeanIsCaseMeanStatement)
    (hC : caseMeanProperties) (hK : BondKernelProperties)
    (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) : conditionalMeanReadsCasesStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt₀, H⟩ := hG a ha
  refine ⟨L₀, rt₀, hrt₀, fun L hodd hL Tb hTa hTL hD hr => ?_⟩
  obtain ⟨y₀, Y⟩ := H L hodd hL Tb hTa hTL hD hr
  refine ⟨y₀, fun y hy hret hwil T β s n _ hst hcut hcoin hform hbs hdvd => ?_⟩
  have hf : (Tb.stepParameters y).Admissible := hform.admissible
  have hP : IsProbabilityMeasure (markedSampleLaw T β (s + 1) n) :=
    (hT _ hf hf.depth_lt T hcut hcoin β (fun _ => 0) (s + 1) n).1
  have hw : ∀ (C : Finset (TorusSite n)) (V : TorusField n) W Yt ωt bad b, 0 ≤ StepSettings.stepWeight (T.stage s).toStepSetup C V W Yt ωt bad b :=
    fun C V W Yt ωt bad b => stepWeight_nonneg hK hst.startsAtWilson hcut s n C V W Yt ωt bad b
  have hMG : ∀ F : TorusField n → WeightedResponses.CaseFunction (T.stage s).toStepSetup n, Measurable (caseLift T s n F) →
      (∃ C : ℝ, ∀ x, |caseLift T s n F x| ≤ C) →
      (markedSampleLaw T β (s + 1) n)[caseLift T s n F | stageSigma T (s + 1) n] =ᵐ[markedSampleLaw T β (s + 1) n] caseMeanAtSample T s n F :=
    fun F hm hb => Y y hy hret hwil T β s n hst hcut hcoin hform hbs hdvd F hm hb
  refine ⟨hw, fun hone => ⟨fun F hm K hK' hI => condExp_eq_caseMean_of_ae_bounded hC s n hMG hw hone hm hK' hI, ?_⟩⟩
  intro φ hφ hm hI D K hD' hK' hle
  exact abs_condExp_le_caseMean hC s n hMG hw hone hφ hm hI hD' hK' hle
end YangMills.Construction.FreeEnergies
end
