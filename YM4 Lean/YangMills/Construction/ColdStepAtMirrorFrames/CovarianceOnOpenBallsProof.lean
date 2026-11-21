import YangMills.Construction.ColdStepAtMirrorFrames.CovarianceOnOpenBalls
import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenInValueProofForm
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace OpenPolyballCutoff
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ}
theorem openPolyball_eq_ball (hρ : 0 < ρ) : openPolyball ι ρ = Metric.ball (0 : BondField ι) ρ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.openPolyball_eq_ball <;> assumption
theorem isOpen_openPolyball (hρ : 0 < ρ) : IsOpen (openPolyball ι ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.isOpen_openPolyball <;> assumption
def dilationFactor (n : ℕ) : ℝ := (1 + 1 / ((n : ℝ) + 1))⁻¹
theorem dilationFactor_pos (n : ℕ) : 0 < dilationFactor n := by
  unfold dilationFactor
  positivity
theorem dilationFactor_le_one (n : ℕ) : dilationFactor n ≤ 1 := by
  unfold dilationFactor
  apply inv_le_one_of_one_le₀
  have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  linarith
theorem tendsto_dilationFactor : Tendsto dilationFactor atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) := h.const_add 1
  have h3 := h2.inv₀ (by norm_num)
  have e : dilationFactor = fun n : ℕ => (1 + 1 / ((n : ℝ) + 1))⁻¹ := rfl
  rw [e]
  simpa using h3
def dilationBump (hρ : 0 < ρ) (n : ℕ) : ContDiffBump (0 : BondField ι) where
  rIn := ρ * (1 + (1 / ((n : ℝ) + 1)) / 3)
  rOut := ρ * (1 + 2 * (1 / ((n : ℝ) + 1)) / 3)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    apply mul_lt_mul_of_pos_left _ hρ
    linarith
def dilatedCutoff (hρ : 0 < ρ) (f : BondField ι → ℝ) (n : ℕ) (η : BondField ι) : ℝ :=
  (dilationBump (ι := ι) hρ n) η * f (dilationFactor n • η)
theorem contDiff_dilationBump (hρ : 0 < ρ) (n : ℕ) : ContDiff ℝ 1 (dilationBump (ι := ι) hρ n) :=
  ((dilationBump (ι := ι) hρ n).contDiff (n := ⊤)).of_le (by exact_mod_cast le_top)
theorem dilationFactor_smul_mem (hρ : 0 < ρ) {n : ℕ} {η : BondField ι}
    (h : ‖η‖ < ρ * (1 + 1 / ((n : ℝ) + 1))) : dilationFactor n • η ∈ openPolyball ι ρ := by
  rw [openPolyball_eq_ball hρ, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (dilationFactor_pos n)]
  unfold dilationFactor
  have hp : 0 < 1 + 1 / ((n : ℝ) + 1) := by positivity
  rw [inv_mul_lt_iff₀ hp]
  linarith
theorem contDiff_dilatedCutoff (hρ : 0 < ρ) {f : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ)) (n : ℕ) :
    ContDiff ℝ 1 (dilatedCutoff hρ f n) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  have hpn : 0 < 1 / ((n : ℝ) + 1) := by positivity
  by_cases hη : ‖η‖ < ρ * (1 + 1 / ((n : ℝ) + 1))
  · have hm := dilationFactor_smul_mem hρ hη
    have h1 : ContDiffAt ℝ 1 f (dilationFactor n • η) := hf.contDiffAt ((isOpen_openPolyball hρ).mem_nhds hm)
    have h2 : ContDiffAt ℝ 1 (fun ζ : BondField ι => dilationFactor n • ζ) η :=
      (contDiff_const_smul (dilationFactor n)).contDiffAt
    have h3 : ContDiffAt ℝ 1 (fun ζ : BondField ι => f (dilationFactor n • ζ)) η := h1.comp η h2
    exact ((contDiff_dilationBump (ι := ι) hρ n).contDiffAt).mul h3
  · have hout : η ∈ (Metric.closedBall (0 : BondField ι) (dilationBump (ι := ι) hρ n).rOut)ᶜ := by
      simp only [Set.mem_compl_iff, mem_closedBall_zero_iff, not_le]
      refine lt_of_lt_of_le ?_ (not_lt.mp hη)
      show ρ * (1 + 2 * (1 / ((n : ℝ) + 1)) / 3) < _
      apply mul_lt_mul_of_pos_left _ hρ
      linarith
    have hev : dilatedCutoff hρ f n =ᶠ[𝓝 η] fun _ => 0 := by
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hout] with ζ hζ
      have : (dilationBump (ι := ι) hρ n) ζ = 0 := by
        apply Function.notMem_support.mp
        rw [(dilationBump (ι := ι) hρ n).support_eq]
        exact fun h => hζ (Metric.ball_subset_closedBall h)
      simp [dilatedCutoff, this]
    exact contDiffAt_const.congr_of_eventuallyEq hev
theorem dilatedCutoff_eventuallyEq (hρ : 0 < ρ) (f : BondField ι → ℝ) (n : ℕ) {η : BondField ι}
    (hη : η ∈ openPolyball ι ρ) : dilatedCutoff hρ f n =ᶠ[𝓝 η] fun ζ => f (dilationFactor n • ζ) := by
  filter_upwards [(isOpen_openPolyball hρ).mem_nhds hη] with ζ hζ
  have hin : ζ ∈ Metric.closedBall (0 : BondField ι) (dilationBump (ι := ι) hρ n).rIn := by
    rw [openPolyball_eq_ball hρ, mem_ball_zero_iff] at hζ
    rw [mem_closedBall_zero_iff]
    have : ρ ≤ (dilationBump (ι := ι) hρ n).rIn := by
      show ρ ≤ ρ * (1 + (1 / ((n : ℝ) + 1)) / 3)
      have hpn : 0 < 1 / ((n : ℝ) + 1) := by positivity
      nlinarith
    linarith
  simp [dilatedCutoff, (dilationBump (ι := ι) hρ n).one_of_mem_closedBall hin]
theorem dilationFactor_smul_mem_openPolyball (hρ : 0 < ρ) {n : ℕ} {η : BondField ι} (hη : η ∈ openPolyball ι ρ) :
    dilationFactor n • η ∈ openPolyball ι ρ := by
  apply dilationFactor_smul_mem hρ
  rw [openPolyball_eq_ball hρ, mem_ball_zero_iff] at hη
  have hpn : 0 < 1 / ((n : ℝ) + 1) := by positivity
  nlinarith
theorem dilatedCutoff_apply (hρ : 0 < ρ) (f : BondField ι → ℝ) (n : ℕ) {η : BondField ι}
    (hη : η ∈ openPolyball ι ρ) : dilatedCutoff hρ f n η = f (dilationFactor n • η) :=
  (dilatedCutoff_eventuallyEq hρ f n hη).self_of_nhds
theorem bondGradNorm_dilatedCutoff (hρ : 0 < ρ) {f : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ)) (n : ℕ)
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) (b : ι) :
    bondGradNorm (dilatedCutoff hρ f n) b η = dilationFactor n * bondGradNorm f b (dilationFactor n • η) := by
  have hm := dilationFactor_smul_mem_openPolyball hρ (n := n) hη
  have h1 : HasFDerivAt f (fderiv ℝ f (dilationFactor n • η)) (dilationFactor n • η) :=
    ((hf.contDiffAt ((isOpen_openPolyball hρ).mem_nhds hm)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt (fun ζ : BondField ι => dilationFactor n • ζ)
      (dilationFactor n • ContinuousLinearMap.id ℝ (BondField ι)) η :=
    (ContinuousLinearMap.id ℝ (BondField ι)).hasFDerivAt.const_smul (dilationFactor n)
  have h3 := h1.comp η h2
  have h4 : fderiv ℝ (dilatedCutoff hρ f n) η =
      (fderiv ℝ f (dilationFactor n • η)).comp (dilationFactor n • ContinuousLinearMap.id ℝ (BondField ι)) := by
    rw [(dilatedCutoff_eventuallyEq hρ f n hη).fderiv_eq]
    exact h3.fderiv
  unfold bondGradNorm
  rw [h4]
  have h5 : ((fderiv ℝ f (dilationFactor n • η)).comp (dilationFactor n • ContinuousLinearMap.id ℝ (BondField ι))).comp
      (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) =
      dilationFactor n • (fderiv ℝ f (dilationFactor n • η)).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) := by
    ext v
    simp
  rw [h5, norm_smul, Real.norm_eq_abs, abs_of_pos (dilationFactor_pos n)]
theorem continuous_bondGradNorm {G : BondField ι → ℝ} (hG : ContDiff ℝ 1 G) (b : ι) :
    Continuous (bondGradNorm G b) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.continuous_gradNorm <;> assumption
theorem continuousOn_bondGradNorm (hρ : 0 < ρ) {f : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ))
    (b : ι) : ContinuousOn (bondGradNorm f b) (openPolyball ι ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.continuousOn_bondGradNorm <;> assumption
theorem tendsto_dilationFactor_smul (hρ : 0 < ρ) {η : BondField ι} (hη : η ∈ openPolyball ι ρ) :
    Tendsto (fun n => dilationFactor n • η) atTop (𝓝[openPolyball ι ρ] η) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => dilationFactor_smul_mem_openPolyball hρ hη⟩
  have := tendsto_dilationFactor.smul_const η
  simpa using this
theorem tendsto_comp_dilationFactor_smul (hρ : 0 < ρ) {f : BondField ι → ℝ} (hf : ContinuousOn f (openPolyball ι ρ))
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) :
    Tendsto (fun n => f (dilationFactor n • η)) atTop (𝓝 (f η)) :=
  (hf η hη).tendsto.comp (tendsto_dilationFactor_smul hρ hη)
section Expectations
variable {r : ℝ → ℝ} {Ψ : BondField ι → ℝ}
theorem tendsto_ballExpectation (hϱc : Integrable (ballDensity r Ψ)) (hϱm : Continuous (ballDensity r Ψ))
    (hϱ0 : ∀ η, η ∉ openPolyball ι ρ → ballDensity r Ψ η = 0) (hϱn : ∀ η, 0 ≤ ballDensity r Ψ η)
    {hs : ℕ → BondField ι → ℝ} {h : BondField ι → ℝ} {C : ℝ}
    (hm : ∀ n, Continuous (hs n)) (hb : ∀ n, ∀ η ∈ openPolyball ι ρ, |hs n η| ≤ C)
    (hl : ∀ η ∈ openPolyball ι ρ, Tendsto (fun n => hs n η) atTop (𝓝 (h η))) :
    Tendsto (fun n => ballExpectation r Ψ (hs n)) atTop (𝓝 (ballExpectation r Ψ h)) := by
  unfold ballExpectation
  apply Tendsto.div_const
  apply tendsto_integral_of_dominated_convergence (fun η => C * ballDensity r Ψ η)
  · exact fun n => ((hm n).mul hϱm).aestronglyMeasurable
  · exact hϱc.const_mul C
  · intro n
    refine Eventually.of_forall fun η => ?_
    by_cases hη : η ∈ openPolyball ι ρ
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hϱn η)]
      exact mul_le_mul_of_nonneg_right (hb n η hη) (hϱn η)
    · simp [hϱ0 η hη]
  · refine Eventually.of_forall fun η => ?_
    by_cases hη : η ∈ openPolyball ι ρ
    · exact (hl η hη).mul_const _
    · simp [hϱ0 η hη]
end Expectations
end OpenPolyballCutoff
open OpenPolyballCutoff in
theorem ballCovarianceBoundOnOpenPolyball_of (h4 : BallCovarianceBound)
    (hrim : CutoffFactorIsRadialCutoff) : BallCovarianceBoundOnOpenPolyball := by
  intro ι _ _ ρ m κ d Ψ K p hρ hm hκ hp hd hΨ f g M hf hg hbd
  have hr := hrim ρ p hρ hp
  set r : ℝ → ℝ := fun u => cutoffFactor ρ p (max u 0) with hrd
  have erim : radialWeightProd (ι := ι) (cutoffFactor ρ p) = radialWeightProd r := by
    funext η
    simp only [radialWeightProd, hrd, max_eq_left (norm_nonneg _)]
  have eden : ballDensity (ι := ι) (cutoffFactor ρ p) Ψ = ballDensity r Ψ := by
    funext η
    simp only [ballDensity, erim]
  have hΨc : Continuous Ψ := hΨ.smooth.continuous
  have hϱm : Continuous (ballDensity (cutoffFactor ρ p) Ψ) := by
    rw [eden]
    unfold ballDensity
    refine Continuous.mul ?_ (hΨc.neg.rexp)
    unfold radialWeightProd
    refine continuous_finset_prod _ fun b _ => ?_
    have h1 : ContDiff ℝ 1 r := hr.smooth
    exact h1.continuous.comp ((continuous_apply b).norm)
  have hϱ0 : ∀ η, η ∉ openPolyball ι ρ → ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
    intro η hη
    rw [eden]
    simp only [openPolyball, Set.mem_ofPred_eq, not_forall, not_lt] at hη
    obtain ⟨b, hb⟩ := hη
    have h0 : ∏ b, r ‖η b‖ = 0 := Finset.prod_eq_zero (Finset.mem_univ b) (hr.zero _ hb)
    simp [ballDensity, radialWeightProd, h0]
  have hϱn : ∀ η, 0 ≤ ballDensity (cutoffFactor ρ p) Ψ η := by
    intro η
    rw [eden]
    refine mul_nonneg (Finset.prod_nonneg fun b _ => ?_) (Real.exp_pos _).le
    rcases lt_or_ge ‖η b‖ ρ with h | h
    · exact (hr.pos _ (norm_nonneg _) h).le
    · rw [hr.zero _ h]
  have hϱc : Integrable (ballDensity (cutoffFactor ρ p) Ψ) := by
    apply hϱm.integrable_of_hasCompactSupport
    refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
    apply hϱ0
    intro h
    apply hη
    rw [openPolyball_eq_ball hρ] at h
    exact Metric.ball_subset_closedBall h
  have hMn : 0 ≤ M := (abs_nonneg _).trans (hbd 0 (fun b => by simpa using hρ)).1
  set F := dilatedCutoff hρ f with hF
  set G := dilatedCutoff hρ g with hG
  have Fs : ∀ n, ContDiff ℝ 1 (F n) := contDiff_dilatedCutoff hρ hf
  have Gs : ∀ n, ContDiff ℝ 1 (G n) := contDiff_dilatedCutoff hρ hg
  have hfc : ContinuousOn f (openPolyball ι ρ) := hf.continuousOn
  have hgc : ContinuousOn g (openPolyball ι ρ) := hg.continuousOn
  have each : ∀ n, |ballCovariance (cutoffFactor ρ p) Ψ (F n) (G n)| ≤ m⁻¹ * ∑ b, ∑ b',
      ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm (F n) b) * Real.exp (-(κ * d b b')) *
        ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm (G n) b') := fun n =>
    h4 ι ρ m κ d Ψ K p hρ hm hκ hp hd hΨ (F n) (G n) (Fs n) (Gs n)
  have tF : Tendsto (fun n => ballExpectation (cutoffFactor ρ p) Ψ (F n)) atTop
      (𝓝 (ballExpectation (cutoffFactor ρ p) Ψ f)) :=
    tendsto_ballExpectation hϱc hϱm hϱ0 hϱn (C := M) (fun n => (Fs n).continuous)
      (fun n η hη => by
        rw [hF, dilatedCutoff_apply hρ f n hη]
        exact (hbd _ (dilationFactor_smul_mem_openPolyball hρ hη)).1)
      (fun η hη => by
        have := tendsto_comp_dilationFactor_smul hρ hfc hη
        refine this.congr fun n => ?_
        rw [hF, dilatedCutoff_apply hρ f n hη])
  have tG : Tendsto (fun n => ballExpectation (cutoffFactor ρ p) Ψ (G n)) atTop
      (𝓝 (ballExpectation (cutoffFactor ρ p) Ψ g)) :=
    tendsto_ballExpectation hϱc hϱm hϱ0 hϱn (C := M) (fun n => (Gs n).continuous)
      (fun n η hη => by
        rw [hG, dilatedCutoff_apply hρ g n hη]
        exact (hbd _ (dilationFactor_smul_mem_openPolyball hρ hη)).2.1)
      (fun η hη => by
        have := tendsto_comp_dilationFactor_smul hρ hgc hη
        refine this.congr fun n => ?_
        rw [hG, dilatedCutoff_apply hρ g n hη])
  have tFG : Tendsto (fun n => ballExpectation (cutoffFactor ρ p) Ψ (fun η => F n η * G n η)) atTop
      (𝓝 (ballExpectation (cutoffFactor ρ p) Ψ fun η => f η * g η)) :=
    tendsto_ballExpectation hϱc hϱm hϱ0 hϱn (C := M * M)
      (fun n => (Fs n).continuous.mul (Gs n).continuous)
      (fun n η hη => by
        rw [hF, hG, dilatedCutoff_apply hρ f n hη, dilatedCutoff_apply hρ g n hη, abs_mul]
        have h1 := hbd _ (dilationFactor_smul_mem_openPolyball (n := n) hρ hη)
        exact mul_le_mul h1.1 h1.2.1 (abs_nonneg _) hMn)
      (fun η hη => by
        have := (tendsto_comp_dilationFactor_smul hρ hfc hη).mul (tendsto_comp_dilationFactor_smul hρ hgc hη)
        refine this.congr fun n => ?_
        rw [hF, hG, dilatedCutoff_apply hρ f n hη, dilatedCutoff_apply hρ g n hη])
  have tN : ∀ {u : BondField ι → ℝ} (U : ℕ → BondField ι → ℝ) (b : ι),
      (∀ n, ContDiff ℝ 1 (U n)) → ContDiffOn ℝ 1 u (openPolyball ι ρ) →
      (∀ n, ∀ η ∈ openPolyball ι ρ, bondGradNorm (U n) b η = dilationFactor n * bondGradNorm u b (dilationFactor n • η)) →
      (∀ η ∈ openPolyball ι ρ, bondGradNorm u b η ≤ M) →
      Tendsto (fun n => ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm (U n) b)) atTop
        (𝓝 (ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm u b))) := by
    intro u U b hU hu hUe hub
    unfold ballL2Norm
    apply (Real.continuous_sqrt.tendsto _).comp
    have hpc := continuousOn_bondGradNorm hρ hu b
    have hnn : ∀ {v : BondField ι → ℝ} {η}, 0 ≤ bondGradNorm v b η := fun {_ _} => norm_nonneg _
    refine tendsto_ballExpectation hϱc hϱm hϱ0 hϱn (C := M ^ 2)
      (fun n => (continuous_bondGradNorm (hU n) b).pow 2) (fun n η hη => ?_) (fun η hη => ?_)
    · rw [hUe n η hη, abs_of_nonneg (by positivity)]
      have h1 : dilationFactor n * bondGradNorm u b (dilationFactor n • η) ≤ M := by
        calc dilationFactor n * bondGradNorm u b (dilationFactor n • η) ≤ 1 * M :=
              mul_le_mul (dilationFactor_le_one n) (hub _ (dilationFactor_smul_mem_openPolyball hρ hη)) hnn (by norm_num)
          _ = M := one_mul M
      have h2 : 0 ≤ dilationFactor n * bondGradNorm u b (dilationFactor n • η) := mul_nonneg (dilationFactor_pos n).le hnn
      exact pow_le_pow_left₀ h2 h1 2
    · have h1 := (tendsto_dilationFactor.mul (tendsto_comp_dilationFactor_smul hρ hpc hη)).pow 2
      simp only [one_mul] at h1
      refine h1.congr fun n => ?_
      rw [hUe n η hη]
  have tNF : ∀ b, Tendsto (fun n => ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm (F n) b)) atTop
      (𝓝 (ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm f b))) := fun b =>
    tN F b Fs hf (fun n η hη => bondGradNorm_dilatedCutoff hρ hf n hη b) (fun η hη => ((hbd η hη).2.2 b).1)
  have tNG : ∀ b, Tendsto (fun n => ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm (G n) b)) atTop
      (𝓝 (ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm g b))) := fun b =>
    tN G b Gs hg (fun n η hη => bondGradNorm_dilatedCutoff hρ hg n hη b) (fun η hη => ((hbd η hη).2.2 b).2)
  have tL : Tendsto (fun n => |ballCovariance (cutoffFactor ρ p) Ψ (F n) (G n)|) atTop
      (𝓝 |ballCovariance (cutoffFactor ρ p) Ψ f g|) := by
    unfold ballCovariance
    exact (tFG.sub (tF.mul tG)).abs
  have tR : Tendsto (fun n => m⁻¹ * ∑ b, ∑ b',
      ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm (F n) b) * Real.exp (-(κ * d b b')) *
        ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm (G n) b')) atTop
      (𝓝 (m⁻¹ * ∑ b, ∑ b',
        ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm f b) * Real.exp (-(κ * d b b')) *
          ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm g b'))) := by
    apply Tendsto.const_mul
    refine tendsto_finset_sum _ fun b _ => tendsto_finset_sum _ fun b' _ => ?_
    exact ((tNF b).mul_const _).mul (tNG b')
  exact le_of_tendsto_of_tendsto' tL tR each
end YangMills.Construction.ColdStepAtMirrorFrames
end
