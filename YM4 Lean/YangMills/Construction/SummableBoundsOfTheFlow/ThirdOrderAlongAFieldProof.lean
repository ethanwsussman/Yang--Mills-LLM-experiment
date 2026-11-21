import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExplicitCumulantsOfMeans
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAFieldInALaw
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderAlongAField
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.BondIntegration YangMills.Construction.Cumulants YangMills.Construction.ConvexObservables YangMills.Construction.Interpolation YangMills.Construction.Estimates
namespace YangMills.Construction.Estimates
namespace QuarticMoments
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
def HasFourthMoment (μ : Measure (BondField ι)) (f : BondField ι → ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ Integrable (fun η => f η ^ 4) μ
variable {μ : Measure (BondField ι)} [IsProbabilityMeasure μ] {f g k : BondField ι → ℝ}
theorem HasFourthMoment.sq_memLp (hf : HasFourthMoment μ f) : MemLp (fun η => f η ^ 2) 2 μ := by
  refine (memLp_two_iff_integrable_sq (hf.1.pow 2)).2 ?_
  refine hf.2.congr (Filter.Eventually.of_forall fun η => ?_)
  simp only [Pi.pow_apply]
  ring
theorem HasFourthMoment.memLp (hf : HasFourthMoment μ f) : MemLp f 2 μ :=
  (memLp_two_iff_integrable_sq hf.1).2 ((HasFourthMoment.sq_memLp hf).integrable (by norm_num))
theorem HasFourthMoment.integrable (hf : HasFourthMoment μ f) : Integrable f μ :=
  (HasFourthMoment.memLp hf).integrable (by norm_num)
theorem HasFourthMoment.integrable_mul (hf : HasFourthMoment μ f) (hg : HasFourthMoment μ g) :
    Integrable (fun η => f η * g η) μ :=
  (HasFourthMoment.memLp hf).integrable_mul (HasFourthMoment.memLp hg)
theorem HasFourthMoment.integrable_mul_mul (hf : HasFourthMoment μ f) (hg : HasFourthMoment μ g)
    (hk : HasFourthMoment μ k) : Integrable (fun η => f η * g η * k η) μ := by
  have h1 : MemLp (fun η => f η * g η) 2 μ := by
    refine (memLp_two_iff_integrable_sq (hf.1.mul hg.1)).2 ?_
    refine ((HasFourthMoment.sq_memLp hf).integrable_mul (HasFourthMoment.sq_memLp hg)).congr
      (Filter.Eventually.of_forall fun η => ?_)
    simp only [Pi.mul_apply]
    ring
  exact h1.integrable_mul (HasFourthMoment.memLp hk)
theorem add_pow_four_le_eight_mul (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.add_pow_four_le_eight_mul <;> assumption
theorem HasFourthMoment.add_const (hf : HasFourthMoment μ f) (c : ℝ) :
    HasFourthMoment μ (fun η => f η + c) := by
  refine ⟨hf.1.add aestronglyMeasurable_const, ?_⟩
  have hb : Integrable (fun η => 8 * (f η ^ 4 + c ^ 4)) μ :=
    (hf.2.add (integrable_const _)).const_mul 8
  refine hb.mono' ((hf.1.add aestronglyMeasurable_const).pow 4) (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact add_pow_four_le_eight_mul _ _
theorem HasFourthMoment.add_of_abs_le (hf : HasFourthMoment μ f) (hg : AEStronglyMeasurable g μ) {M : ℝ}
    (h : ∀ᵐ η ∂μ, |g η| ≤ M) : HasFourthMoment μ (fun η => f η + g η) := by
  refine ⟨hf.1.add hg, ?_⟩
  have hb : Integrable (fun η => 8 * (f η ^ 4 + M ^ 4)) μ :=
    (hf.2.add (integrable_const _)).const_mul 8
  refine hb.mono' ((hf.1.add hg).pow 4) ?_
  filter_upwards [h] with η hη
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine (add_pow_four_le_eight_mul _ _).trans ?_
  have h1 : g η ^ 4 ≤ M ^ 4 := by
    have h2 : |g η| ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hη 4
    have e1 : |g η| ^ 4 = g η ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
    rwa [e1] at h2
  linarith
theorem HasFourthMoment.of_abs_le_mul (hf : HasFourthMoment μ f) (hg : AEStronglyMeasurable g μ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ᵐ η ∂μ, |g η| ≤ C * |f η|) : HasFourthMoment μ g := by
  refine ⟨hg, ?_⟩
  refine (hf.2.const_mul (C ^ 4)).mono' (hg.pow 4) ?_
  filter_upwards [h] with η hη
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : |g η| ^ 4 ≤ (C * |f η|) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hη 4
  have e1 : |g η| ^ 4 = g η ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  have e2 : (C * |f η|) ^ 4 = C ^ 4 * f η ^ 4 := by
    rw [mul_pow, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul |f η|, sq_abs, ← pow_mul]
  rw [← e1]
  linarith
end QuarticMoments
set_option maxHeartbeats 2000000 in
open QuarticMoments in
theorem covarianceWithFieldDerivativeDecay_of_cumulants (hC : Cumulants.cumulantDecayBound)
    (hE : Cumulants.lowOrderCumulantFormulas) (hm : BondIntegration.integrationByPartsAlongFieldStatement)
    (hlaw : ConvexObservables.normalizedBallLawIsProbabilityStatement) :
    Estimates.CovarianceWithFieldDerivativeDecay := by
  intro N κ lam hκ hlam
  obtain ⟨Tn, hTn, hcum⟩ := hC N κ lam hκ hlam
  refine ⟨Tn, hTn, ?_⟩
  intro F ι _ _ y ρ x p Ψ K hρ hx hp hN hK hsl A H R z Y Z CA CH CS α h h' s w u hCA hCH hCS hα hh hh' hs
    hw hu dA dH dR dAb dS sA sAb sH sR sS hby
  have hΨ : ContDiff ℝ 1 Ψ := hK.smooth.of_le (by norm_num)
  have cΨ : Continuous Ψ := hΨ.continuous
  obtain ⟨l1, l2, l3, l4, -⟩ := hlaw ι ρ p Ψ hρ hp cΨ
  haveI := l1
  have hopen : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    have : {η : BondField ι | ∀ b, ‖η b‖ < ρ} = ⋂ b, {η | ‖η b‖ < ρ} := by
      ext η
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have aesm : ∀ {f : BondField ι → ℝ}, ContinuousOn f {η | ∀ b, ‖η b‖ < ρ} →
      AEStronglyMeasurable f (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
    intro f hf
    have l4' : ∀ᵐ η ∂(normalizedBallLaw (cutoffFactor ρ p) Ψ), η ∈ {η : BondField ι | ∀ b, ‖η b‖ < ρ} := l4
    have h0 := Measure.restrict_eq_self_of_ae_mem l4'
    rw [← h0]
    exact hf.aestronglyMeasurable hopen.measurableSet
  have fromMoment : ∀ {f : BondField ι → ℝ} {B : ℝ}, ContinuousOn f {η | ∀ b, ‖η b‖ < ρ} →
      MomentBound (cutoffFactor ρ p) Ψ f 4 B → HasFourthMoment (normalizedBallLaw (cutoffFactor ρ p) Ψ) f := by
    intro f B hc hb
    refine ⟨aesm hc, ?_⟩
    refine ((l3 _).2 hb.1).congr (Filter.Eventually.of_forall fun η => ?_)
    simp only
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  have ofSize : ∀ {Cq : ℕ → ℝ} {a : ℝ} {dZ : ι → ℝ} {f : BondField ι → ℝ},
      ContinuousOn f {η | ∀ b, ‖η b‖ < ρ} → HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ a dZ f →
        HasFourthMoment (normalizedBallLaw (cutoffFactor ρ p) Ψ) f := by
    intro Cq a dZ f hc hs₀
    obtain ⟨-, f₀, hmo⟩ := hs₀
    have h1 := fromMoment (hc.sub continuousOn_const) (hmo 4 (by norm_num)).1
    have h2 := h1.add_const f₀
    refine ⟨aesm hc, ?_⟩
    refine h2.2.congr (Filter.Eventually.of_forall fun η => ?_)
    simp
  have partial_cont : ∀ {f : BondField ι → ℝ}, ContDiffOn ℝ 1 f {η | ∀ b, ‖η b‖ < ρ} → ∀ b,
      ContinuousOn (bondGradNorm f b) {η | ∀ b, ‖η b‖ < ρ} := by
    intro f hf b
    have h1 := hf.continuousOn_fderiv_of_isOpen hopen le_rfl
    unfold bondGradNorm
    exact (h1.clm_comp continuousOn_const).norm
  have along_cont : ∀ {f : BondField ι → ℝ}, ContDiffOn ℝ 1 f {η | ∀ b, ‖η b‖ < ρ} → ∀ b,
      ContinuousOn (fieldDerivative b (z b) f) {η | ∀ b, ‖η b‖ < ρ} := by
    intro f hf b
    have h1 := hf.continuousOn_fderiv_of_isOpen hopen le_rfl
    have hz : Continuous (z b) := (hby b).contDiff.continuous
    have h2 : Continuous fun η : BondField ι => bondVariation b (z b (η b)) := by
      have e : (fun η : BondField ι => bondVariation b (z b (η b))) =
          fun η => ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b (z b (η b)) := by
        funext η
        rfl
      rw [e]
      exact (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).continuous.comp
        (hz.comp (continuous_apply b))
    exact h1.clm_apply h2.continuousOn
  have along_bound : ∀ (f : BondField ι → ℝ) (b : ι) (C : ℝ), (∀ v, ‖z b v‖ ≤ C) → ∀ η,
      |fieldDerivative b (z b) f η| ≤ C * |bondGradNorm f b η| := by
    intro f b C hb η
    have h1 := ((fderiv ℝ f η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)).le_opNorm
      (z b (η b))
    have h2 : |fieldDerivative b (z b) f η| ≤ bondGradNorm f b η * ‖z b (η b)‖ := by
      simpa [fieldDerivative, bondPartialDeriv, bondGradNorm, bondVariation, Real.norm_eq_abs] using h1
    have h3 : 0 ≤ bondGradNorm f b η := norm_nonneg _
    rw [abs_of_nonneg h3]
    calc |fieldDerivative b (z b) f η| ≤ bondGradNorm f b η * ‖z b (η b)‖ := h2
      _ ≤ bondGradNorm f b η * C := mul_le_mul_of_nonneg_left (hb _) h3
      _ = _ := mul_comm _ _
  have cA := dA.continuousOn
  have cH := dH.continuousOn
  have cR := dR.continuousOn
  have iA := ofSize cA sA
  have iH := ofSize cH sH
  have iR := ofSize cR sR
  have iAb := fun b => ofSize (dAb b).continuousOn (sAb b)
  have iS := fun b => ofSize (dS b).continuousOn (sS b)
  have iHb : ∀ b, HasFourthMoment (normalizedBallLaw (cutoffFactor ρ p) Ψ) (fieldDerivative b (z b) H) := by
    intro b
    obtain ⟨C, hCz, -⟩ := (hby b).bounded
    obtain ⟨-, f₀, hmo⟩ := sH
    have h1 := fromMoment (partial_cont dH b) ((hmo 4 (by norm_num)).2 b)
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCz 0)
    exact h1.of_abs_le_mul (aesm (along_cont dH b)) hC0
      (Filter.Eventually.of_forall (along_bound H b C hCz))
  have hΨd := hΨ.continuous_fderiv (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have boundOn : ∀ {f : BondField ι → ℝ}, Continuous f → ∃ M, ∀ η : BondField ι,
      (∀ b, ‖η b‖ < ρ) → |f η| ≤ M := by
    intro f hf
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_bound_of_continuousOn
      hf.continuousOn
    refine ⟨M, fun η hη => ?_⟩
    have : η ∈ Metric.closedBall (0 : BondField ι) ρ := by
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg hρ.le).2 fun c => (hη c).le
    simpa using hM η this
  have iRim : ∀ b, HasFourthMoment (normalizedBallLaw (cutoffFactor ρ p) Ψ)
      (fun η => radialCutoffSlope p (η b) (z b (η b))) := by
    intro b
    have hzc : Continuous (z b) := (hby b).contDiff.continuous
    have hdc := (hby b).contDiff.continuous_fderiv (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hpr : Continuous fun η : BondField ι => η b := continuous_apply b
    have hdiv : Continuous fun η : BondField ι => bondDivergence (z b) (η b) := by
      unfold bondDivergence
      refine continuous_finset_sum _ fun i _ => ?_
      exact (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).continuous.comp
        ((hdc.comp hpr).clm_apply continuous_const)
    have hat : Continuous fun η : BondField ι => bondVariation b (z b (η b)) := by
      have e : (fun η : BondField ι => bondVariation b (z b (η b))) =
          fun η => ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b (z b (η b)) := by
        funext η
        rfl
      rw [e]
      exact (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).continuous.comp (hzc.comp hpr)
    have hg : Continuous fun η : BondField ι =>
        bondDivergence (z b) (η b) - bondPartialDeriv Ψ b η (z b (η b)) :=
      hdiv.sub (hΨd.clm_apply hat)
    obtain ⟨Mg, hMg⟩ := boundOn hg
    have h1 := (iS b).add_of_abs_le hg.aestronglyMeasurable (M := Mg) (by
      have l4' : ∀ᵐ η ∂(normalizedBallLaw (cutoffFactor ρ p) Ψ), ∀ b, ‖η b‖ < ρ := l4
      filter_upwards [l4'] with η hη
      exact hMg η hη)
    refine ⟨?_, ?_⟩
    · refine h1.1.congr (Filter.Eventually.of_forall fun η => ?_)
      simp only [fieldScore]
      ring
    · refine h1.2.congr (Filter.Eventually.of_forall fun η => ?_)
      simp only [fieldScore]
      ring_nf
  have hscore : ∀ b, ballExpectation (cutoffFactor ρ p) Ψ (fieldScore p Ψ b (z b)) = 0 := by
    intro b
    obtain ⟨C, hCz, hCd⟩ := (hby b).bounded
    have e0 : ∀ η, fieldDerivative b (z b) (fun _ : BondField ι => (1 : ℝ)) η = 0 := by
      intro η
      simp [fieldDerivative, bondPartialDeriv]
    have key := hm ι ρ p Ψ (fun _ => 1) b (z b) C hρ hp hΨ contDiffOn_const
      (hby b).contDiff hCz hCd
      (by simp only [e0, zero_mul]; exact integrable_zero _ _ _)
      (by
        have := (l3 _).1 (iS b).integrable
        simpa only [one_mul] using this)
      (by
        have := (l3 _).1 (iRim b).integrable
        simpa only [one_mul] using this)
    simp only [e0, zero_mul, integral_zero, one_mul] at key
    unfold ballExpectation
    rw [← key, zero_div]
  set a := ballExpectation (cutoffFactor ρ p) Ψ A with ha
  set m := ballExpectation (cutoffFactor ρ p) Ψ H with hmH
  have third : ∀ b, ballExpectation (cutoffFactor ρ p) Ψ
      (fun η => (A η - a) * (H η - m) * fieldScore p Ψ b (z b) η) =
      ballThirdCumulant (cutoffFactor ρ p) Ψ A H (fieldScore p Ψ b (z b)) := by
    intro b
    set S := fieldScore p Ψ b (z b) with hSd
    have iSb := iS b
    have e1 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => (A η - a) * (H η - m) * S η) =
        ballExpectation (cutoffFactor ρ p) Ψ (fun η => A η * H η * S η) -
          a * ballExpectation (cutoffFactor ρ p) Ψ (fun η => H η * S η) -
          m * ballExpectation (cutoffFactor ρ p) Ψ (fun η => A η * S η) +
          a * m * ballExpectation (cutoffFactor ρ p) Ψ S := by
      simp only [← l2]
      have q1 := HasFourthMoment.integrable_mul_mul iA iH iSb
      have q2 : Integrable (fun η => a * (H η * S η)) (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
        (HasFourthMoment.integrable_mul iH iSb).const_mul a
      have q3 : Integrable (fun η => m * (A η * S η)) (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
        (HasFourthMoment.integrable_mul iA iSb).const_mul m
      have q4 : Integrable (fun η => a * m * S η) (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
        iSb.integrable.const_mul (a * m)
      have q5 : Integrable (fun η => A η * H η * S η - a * (H η * S η))
          (normalizedBallLaw (cutoffFactor ρ p) Ψ) := q1.sub q2
      have q6 : Integrable (fun η => A η * H η * S η - a * (H η * S η) - m * (A η * S η))
          (normalizedBallLaw (cutoffFactor ρ p) Ψ) := q5.sub q3
      have e : (fun η => (A η - a) * (H η - m) * S η) =
          fun η => A η * H η * S η - a * (H η * S η) - m * (A η * S η) + a * m * S η := by
        funext η
        ring
      rw [e, integral_add q6 q4, integral_sub q5 q3, integral_sub q1 q2, integral_const_mul,
        integral_const_mul, integral_const_mul]
    rw [e1, hscore b]
    unfold ballThirdCumulant
    rw [hscore b, ← ha, ← hmH]
    ring
  have comm : ∀ f g : BondField ι → ℝ,
      ballCovariance (cutoffFactor ρ p) Ψ f g = ballCovariance (cutoffFactor ρ p) Ψ g f := by
    intro f g
    unfold ballCovariance
    have : (fun η => f η * g η) = fun η => g η * f η := by
      funext η
      ring
    rw [this]
    ring
  have per_bond : ∀ b, ballCovariance (cutoffFactor ρ p) Ψ A (fieldDerivative b (z b) H) =
      ballThirdCumulant (cutoffFactor ρ p) Ψ A H (fieldScore p Ψ b (z b)) -
        ballCovariance (cutoffFactor ρ p) Ψ H (fieldDerivative b (z b) A) := by
    intro b
    obtain ⟨C, hCz, hCd⟩ := (hby b).bounded
    have iG : HasFourthMoment (normalizedBallLaw (cutoffFactor ρ p) Ψ) (fun η => A η - a) := by
      have := iA.add_const (-a)
      simpa [sub_eq_add_neg] using this
    have iG' : HasFourthMoment (normalizedBallLaw (cutoffFactor ρ p) Ψ) (fun η => H η - m) := by
      have := iH.add_const (-m)
      simpa [sub_eq_add_neg] using this
    set W := ballDensity (cutoffFactor ρ p) Ψ with hW
    set G : BondField ι → ℝ := fun η => (A η - a) * (H η - m) with hG
    have hGs : ContDiffOn ℝ 1 G {η | ∀ b, ‖η b‖ < ρ} :=
      (dA.sub contDiffOn_const).mul (dH.sub contDiffOn_const)
    have iAb' := (l3 _).1 (iAb b).integrable
    have iHb' := (l3 _).1 (iHb b).integrable
    have iHA := (l3 _).1 (HasFourthMoment.integrable_mul iH (iAb b))
    have iAH := (l3 _).1 (HasFourthMoment.integrable_mul iA (iHb b))
    have hpt : ∀ η, fieldDerivative b (z b) G η * W η =
        H η * fieldDerivative b (z b) A η * W η - m * (fieldDerivative b (z b) A η * W η) +
          (A η * fieldDerivative b (z b) H η * W η - a * (fieldDerivative b (z b) H η * W η)) := by
      intro η
      by_cases hη : ∀ b, ‖η b‖ < ρ
      · have d1 : DifferentiableAt ℝ A η :=
          (dA.contDiffAt (hopen.mem_nhds hη)).differentiableAt (by norm_num)
        have d2 : DifferentiableAt ℝ H η :=
          (dH.contDiffAt (hopen.mem_nhds hη)).differentiableAt (by norm_num)
        have hd := ((d1.hasFDerivAt.sub_const a).mul (d2.hasFDerivAt.sub_const m)).fderiv
        have e : fieldDerivative b (z b) G η =
            (A η - a) * fieldDerivative b (z b) H η + (H η - m) * fieldDerivative b (z b) A η := by
          unfold fieldDerivative bondPartialDeriv
          have : fderiv ℝ G η = _ := hd
          rw [this]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [e]
        ring
      · have h0 : W η = 0 := by
          obtain ⟨c, hc⟩ := not_forall.1 hη
          have : radialWeightProd (cutoffFactor ρ p) η = 0 := by
            refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
            unfold cutoffFactor
            rw [if_neg hc]
          simp [hW, ballDensity, this]
        simp [h0]
    have q1 : Integrable (fun η => H η * fieldDerivative b (z b) A η * W η -
        m * (fieldDerivative b (z b) A η * W η)) :=
      iHA.sub (iAb'.const_mul m)
    have q2 : Integrable (fun η => A η * fieldDerivative b (z b) H η * W η -
        a * (fieldDerivative b (z b) H η * W η)) :=
      iAH.sub (iHb'.const_mul a)
    have q3 : Integrable (fun η => m * (fieldDerivative b (z b) A η * W η)) := iAb'.const_mul m
    have q4 : Integrable (fun η => a * (fieldDerivative b (z b) H η * W η)) := iHb'.const_mul a
    have iAlong : Integrable (fun η => fieldDerivative b (z b) G η * W η) :=
      (q1.add q2).congr (Filter.Eventually.of_forall fun η => (hpt η).symm)
    have key := hm ι ρ p Ψ G b (z b) C hρ hp hΨ hGs (hby b).contDiff hCz hCd iAlong
      ((l3 _).1 (HasFourthMoment.integrable_mul_mul iG iG' (iS b)))
      ((l3 _).1 (HasFourthMoment.integrable_mul_mul iG iG' (iRim b)))
    have e1 : ∫ η, fieldDerivative b (z b) G η * W η =
        ((∫ η, H η * fieldDerivative b (z b) A η * W η) - m * ∫ η, fieldDerivative b (z b) A η * W η) +
          ((∫ η, A η * fieldDerivative b (z b) H η * W η) - a * ∫ η, fieldDerivative b (z b) H η * W η) := by
      simp only [hpt]
      rw [integral_add q1 q2, integral_sub iHA q3, integral_sub iAH q4, integral_const_mul,
        integral_const_mul]
    rw [← third b]
    unfold ballCovariance ballExpectation
    simp only [← hW]
    change _ - a * _ = _ - (_ - m * _)
    have e2 : ∫ η, G η * fieldScore p Ψ b (z b) η * W η =
        ∫ η, (A η - a) * (H η - m) * fieldScore p Ψ b (z b) η * W η := rfl
    rw [key, e2] at e1
    rw [e1]
    ring
  have split : ballCovariance (cutoffFactor ρ p) Ψ A (fun η => (∑ b, fieldDerivative b (z b) H η) + R η) =
      (∑ b, ballCovariance (cutoffFactor ρ p) Ψ A (fieldDerivative b (z b) H)) +
        ballCovariance (cutoffFactor ρ p) Ψ A R := by
    unfold ballCovariance
    have e1 : ballExpectation (cutoffFactor ρ p) Ψ
        (fun η => A η * ((∑ b, fieldDerivative b (z b) H η) + R η)) =
        (∑ b, ballExpectation (cutoffFactor ρ p) Ψ (fun η => A η * fieldDerivative b (z b) H η)) +
          ballExpectation (cutoffFactor ρ p) Ψ (fun η => A η * R η) := by
      simp only [← l2]
      have e : (fun η => A η * ((∑ b, fieldDerivative b (z b) H η) + R η)) =
          fun η => (∑ b, A η * fieldDerivative b (z b) H η) + A η * R η := by
        funext η
        rw [mul_add, Finset.mul_sum]
      rw [e, integral_add (integrable_finset_sum _ fun b _ => HasFourthMoment.integrable_mul iA (iHb b))
          (HasFourthMoment.integrable_mul iA iR),
        integral_finset_sum _ fun b _ => HasFourthMoment.integrable_mul iA (iHb b)]
    have e2 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => (∑ b, fieldDerivative b (z b) H η) + R η) =
        (∑ b, ballExpectation (cutoffFactor ρ p) Ψ (fieldDerivative b (z b) H)) +
          ballExpectation (cutoffFactor ρ p) Ψ R := by
      simp only [← l2]
      rw [integral_add (integrable_finset_sum _ fun b _ => (iHb b).integrable) iR.integrable,
        integral_finset_sum _ fun b _ => (iHb b).integrable]
    rw [e1, e2, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
    ring
  obtain ⟨-, e3, -⟩ : _ ∧ _ ∧ _ := hE ι (cutoffFactor ρ p) Ψ
  have e2 := (hE ι (cutoffFactor ρ p) Ψ).1
  have mono : ∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → sizeConstantSum Cq 2 ≤ sizeConstantSum Cq 3 := by
    intro Cq hq
    unfold sizeConstantSum
    have : ∑ q ∈ Finset.range (2 * 2 + 1), Cq q ≤ ∑ q ∈ Finset.range (2 * 3 + 1), Cq q :=
      Finset.sum_le_sum_of_subset_of_nonneg (by
        intro q hq'
        simp only [Finset.mem_range] at hq' ⊢
        omega) (fun q _ _ => hq q)
    linarith
  have pos3 : ∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → ∀ M, 0 ≤ sizeConstantSum Cq M := by
    intro Cq hq M
    unfold sizeConstantSum
    have : 0 ≤ ∑ q ∈ Finset.range (2 * M + 1), Cq q := Finset.sum_nonneg fun q _ => hq q
    linarith
  set cA := sizeConstantSum CA 3 with hcA
  set cH := sizeConstantSum CH 3 with hcH
  set cS := sizeConstantSum CS 3 with hcS
  have cA0 : 0 ≤ cA := pos3 CA hCA 3
  have cH0 : 0 ≤ cH := pos3 CH hCH 3
  have cS0 : 0 ≤ cS := pos3 CS hCS 3
  have b3 : ∀ b, |ballThirdCumulant (cutoffFactor ρ p) Ψ A H (fieldScore p Ψ b (z b))| ≤
      Tn * (cA * α) * (cH * h) * (cS * (s * u b)) *
        Real.exp (-(κ / 8 * cellsDiameter ![Y, Z, y b])) := by
    intro b
    have h1 := (hcum F ι y ρ x p Ψ K hρ hx hp hN hK hsl 3 ![A, H, fieldScore p Ψ b (z b)] ![Y, Z, y b]
      ![α, h, s * u b] ![CA, CH, CS] (by norm_num) (by norm_num)
      (by
        intro i
        fin_cases i
        · exact dA
        · exact dH
        · exact dS b)
      (by
        intro i
        fin_cases i
        · exact hα
        · exact hh
        · exact mul_nonneg hs (hu b))
      (by
        intro i q
        fin_cases i
        · exact hCA q
        · exact hCH q
        · exact hCS q)
      (by
        intro i
        fin_cases i
        · exact sA
        · exact sH
        · exact sS b)).2
    rw [e3] at h1
    simp only [Fin.prod_univ_three] at h1
    have := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at this
    refine this.trans (le_of_eq ?_)
    ring
  have b2 : ∀ {f g : BondField ι → ℝ} {Cf Cg : ℕ → ℝ} {af ag : ℝ}, (∀ q, 0 ≤ Cf q) → (∀ q, 0 ≤ Cg q) →
      0 ≤ af → 0 ≤ ag → ContDiffOn ℝ 1 f {η | ∀ b, ‖η b‖ < ρ} → ContDiffOn ℝ 1 g {η | ∀ b, ‖η b‖ < ρ} →
      HasLocalSize ρ (cutoffFactor ρ p) Ψ Cf x κ af (fun b => (cellSupDist (y b) Y : ℝ)) f →
      HasLocalSize ρ (cutoffFactor ρ p) Ψ Cg x κ ag (fun b => (cellSupDist (y b) Z : ℝ)) g →
      |ballCovariance (cutoffFactor ρ p) Ψ f g| ≤ Tn * (sizeConstantSum Cf 3 * af) * (sizeConstantSum Cg 3 * ag) *
        Real.exp (-(κ / 8 * cellsDiameter ![Y, Z])) := by
    intro f g Cf Cg af ag hf hg haf hag df dg sf sg
    have h1 := (hcum F ι y ρ x p Ψ K hρ hx hp hN hK hsl 2 ![f, g] ![Y, Z] ![af, ag] ![Cf, Cg]
      (by norm_num) (by norm_num)
      (by
        intro i
        fin_cases i
        · exact df
        · exact dg)
      (by
        intro i
        fin_cases i
        · exact haf
        · exact hag)
      (by
        intro i q
        fin_cases i
        · exact hf q
        · exact hg q)
      (by
        intro i
        fin_cases i
        · exact sf
        · exact sg)).2
    rw [e2] at h1
    simp only [Fin.prod_univ_two] at h1
    have h2 := h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h2
    refine h2.trans ?_
    have hexp := (Real.exp_pos (-(κ / 8 * (cellsDiameter ![Y, Z] : ℝ)))).le
    apply mul_le_mul_of_nonneg_right _ hexp
    have m1 := mono Cf hf
    have m2 := mono Cg hg
    have p1 := pos3 Cf hf 2
    have p2 := pos3 Cg hg 2
    have p3 := pos3 Cf hf 3
    have p4 := pos3 Cg hg 3
    have h3 : sizeConstantSum Cf 2 * af * (sizeConstantSum Cg 2 * ag) ≤
        sizeConstantSum Cf 3 * af * (sizeConstantSum Cg 3 * ag) :=
      mul_le_mul (mul_le_mul_of_nonneg_right m1 haf) (mul_le_mul_of_nonneg_right m2 hag)
        (by positivity) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 hTn
    linarith
  have iFl : Integrable (fun η => (∑ b, fieldDerivative b (z b) H η) + R η)
      (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
    (integrable_finset_sum _ fun b _ => (iHb b).integrable).add iR.integrable
  have iAFl : Integrable (fun η => A η * ((∑ b, fieldDerivative b (z b) H η) + R η))
      (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
    have e : (fun η => A η * ((∑ b, fieldDerivative b (z b) H η) + R η)) =
        fun η => (∑ b, A η * fieldDerivative b (z b) H η) + A η * R η := by
      funext η
      rw [mul_add, Finset.mul_sum]
    rw [e]
    exact (integrable_finset_sum _ fun b _ => HasFourthMoment.integrable_mul iA (iHb b)).add
      (HasFourthMoment.integrable_mul iA iR)
  refine ⟨(l3 _).1 iFl, (l3 _).1 iAFl, ?_⟩
  rw [split]
  set E₂ := Real.exp (-(κ / 8 * cellsDiameter ![Y, Z])) with hE₂
  have hE0 : 0 ≤ E₂ := (Real.exp_pos _).le
  have b4 : ∀ b, |ballCovariance (cutoffFactor ρ p) Ψ A (fieldDerivative b (z b) H)| ≤
      Tn * (cA * α) * (cH * h) * (cS * (s * u b)) *
          Real.exp (-(κ / 8 * cellsDiameter ![Y, Z, y b])) +
        Tn * (cA * (α * w b)) * (cH * h) * E₂ := by
    intro b
    rw [per_bond b, comm H]
    refine (abs_sub _ _).trans (add_le_add (b3 b) ?_)
    exact b2 hCA hCH (mul_nonneg hα (hw b)) hh (dAb b) dH (sAb b) sH
  have b5 := b2 hCA hCH hα hh' dA dR sA sR
  refine (abs_add_le _ _).trans ?_
  have s1 : |∑ b, ballCovariance (cutoffFactor ρ p) Ψ A (fieldDerivative b (z b) H)| ≤
      ∑ b, (Tn * (cA * α) * (cH * h) * (cS * (s * u b)) *
          Real.exp (-(κ / 8 * cellsDiameter ![Y, Z, y b])) +
        Tn * (cA * (α * w b)) * (cH * h) * E₂) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => b4 b)
  refine (add_le_add s1 b5).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib]
  have e5 : ∑ b, Tn * (cA * α) * (cH * h) * (cS * (s * u b)) *
      Real.exp (-(κ / 8 * cellsDiameter ![Y, Z, y b])) =
      Tn * cA * cH * (cS * α * h * s * ∑ b, u b * Real.exp (-(κ / 8 * cellsDiameter ![Y, Z, y b]))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e6 : ∑ b, Tn * (cA * (α * w b)) * (cH * h) * E₂ = Tn * cA * cH * (α * h * (∑ b, w b) * E₂) := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e5, e6]
  ring
end YangMills.Construction.Estimates
end
