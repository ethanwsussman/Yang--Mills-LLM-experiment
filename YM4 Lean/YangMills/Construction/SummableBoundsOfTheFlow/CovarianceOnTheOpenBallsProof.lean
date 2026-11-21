import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenInValueProofForm
import YangMills.Construction.SummableBoundsOfTheFlow.CovarianceOnTheOpenBalls
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace ConvexObservables.OpenBallCovariance
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem isOpen_setOf_norm_lt {ρ : ℝ} (hρ : 0 < ρ) : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.isOpen_openPolyball <;> assumption
theorem ballExpectation_congr {ρ : ℝ} {r : ℝ → ℝ} {Ψ f g : BondField ι → ℝ}
    (hs : ∀ η, ballDensity r Ψ η ≠ 0 → ∀ b, ‖η b‖ < ρ)
    (h : ∀ η, (∀ b, ‖η b‖ < ρ) → f η = g η) : ballExpectation r Ψ f = ballExpectation r Ψ g := by
  unfold ballExpectation
  congr 1
  apply integral_congr_ae
  filter_upwards with η
  by_cases hd : ballDensity r Ψ η = 0
  · rw [hd, mul_zero, mul_zero]
  · rw [h η (hs η hd)]
theorem ballExpectation_const_mul (r : ℝ → ℝ) (Ψ φ : BondField ι → ℝ) (c : ℝ) :
    ballExpectation r Ψ (fun η => c * φ η) = c * ballExpectation r Ψ φ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.expectation_const_mul <;> assumption
theorem tendsto_ballExpectation_smul {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hρ : 0 < ρ)
    (hmeas : Measurable (ballDensity r Ψ))
    (hcont : ContinuousOn (ballDensity r Ψ) {η | ∀ b, ‖η b‖ < ρ})
    (hs : ∀ η, ballDensity r Ψ η ≠ 0 → ∀ b, ‖η b‖ < ρ) (C₀ : ℝ)
    (hdom : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ ζ, ballDensity r Ψ (t⁻¹ • ζ) ≤ C₀ * ballDensity r Ψ ζ)
    (hnn : ∀ η, 0 ≤ ballDensity r Ψ η)
    {φ : BondField ι → ℝ} (hφ : ContinuousOn φ {η | ∀ b, ‖η b‖ < ρ})
    (hi : Integrable fun η => φ η * ballDensity r Ψ η) :
    Tendsto (fun t : ℝ => ballExpectation r Ψ fun η => φ (t • η)) (𝓝[<] 1) (𝓝 (ballExpectation r Ψ φ)) := by
  classical
  set O : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hO
  set D := ballDensity r Ψ with hD
  have hOo : IsOpen O := isOpen_setOf_norm_lt hρ
  set φh : BondField ι → ℝ := O.indicator φ with hφh
  have hφm : Measurable φh := by
    rw [hφh, ← Set.piecewise_eq_indicator]
    exact ContinuousOn.measurable_piecewise hφ continuous_const.continuousOn hOo.measurableSet
  have hφD : ∀ η, φh η * D η = φ η * D η := by
    intro η
    by_cases h : D η = 0
    · rw [h, mul_zero, mul_zero]
    · rw [hφh, Set.indicator_of_mem (show η ∈ O from hs η h)]
  set n := Module.finrank ℝ (BondField ι)
  have hchange : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∫ η, φ (t • η) * D η = |(t ^ n)⁻¹| * ∫ ζ, φh ζ * D (t⁻¹ • ζ) := by
    intro t ht ht1
    have h := Measure.integral_comp_smul volume (fun ζ => φh ζ * D (t⁻¹ • ζ)) t
    rw [smul_eq_mul] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards with η
    rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    by_cases hd : D η = 0
    · rw [hd, mul_zero, mul_zero]
    · have hin : t • η ∈ O := by
        intro b
        have h1 := hs η hd b
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg ht.le]
        nlinarith [norm_nonneg (η b)]
      rw [hφh, Set.indicator_of_mem hin]
  have hdct : Tendsto (fun t : ℝ => ∫ ζ, φh ζ * D (t⁻¹ • ζ)) (𝓝[<] 1) (𝓝 (∫ ζ, φh ζ * D ζ)) := by
    have hev : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t ∧ t ≤ 1 := by
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one (α := ℝ))] with t ht
      exact ⟨ht.1, ht.2.le⟩
    apply tendsto_integral_filter_of_dominated_convergence (fun ζ => |C₀| * |φh ζ * D ζ|)
    · filter_upwards with t
      exact (hφm.mul (hmeas.comp (measurable_const_smul _))).aestronglyMeasurable
    · filter_upwards [hev] with t ht
      refine ae_of_all _ fun ζ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hnn (t⁻¹ • ζ)), abs_of_nonneg (hnn ζ)]
      have h1 := hdom t ht.1 ht.2 ζ
      have h2 : C₀ * D ζ ≤ |C₀| * D ζ := mul_le_mul_of_nonneg_right (le_abs_self _) (hnn ζ)
      calc |φh ζ| * D (t⁻¹ • ζ) ≤ |φh ζ| * (|C₀| * D ζ) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
        _ = _ := by ring
    · have : Integrable fun ζ => φh ζ * D ζ := by
        refine hi.congr (ae_of_all _ fun ζ => ?_)
        exact (hφD ζ).symm
      exact this.abs.const_mul _
    · refine ae_of_all _ fun ζ => ?_
      by_cases hζ : ζ ∈ O
      · apply Tendsto.const_mul
        have hcz : ContinuousAt D ζ := hcont.continuousAt (hOo.mem_nhds hζ)
        have hsm : Tendsto (fun t : ℝ => t⁻¹ • ζ) (𝓝[<] 1) (𝓝 ζ) := by
          have hc : ContinuousAt (fun t : ℝ => t⁻¹ • ζ) 1 :=
            (continuousAt_inv₀ one_ne_zero).smul continuousAt_const
          have h := hc.tendsto
          simp only [inv_one, one_smul] at h
          exact h.mono_left nhdsWithin_le_nhds
        exact hcz.tendsto.comp hsm
      · have : φh ζ = 0 := by rw [hφh, Set.indicator_of_notMem hζ]
        simp only [this, zero_mul]
        exact tendsto_const_nhds
  have hfac : Tendsto (fun t : ℝ => |(t ^ n)⁻¹|) (𝓝[<] 1) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => |(t ^ n)⁻¹|) 1 :=
      ((continuousAt_id.pow n).inv₀ (by simp)).abs
    have h := hc.tendsto
    simp only [one_pow, inv_one, abs_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim := (hfac.mul hdct).div_const (∫ ζ, D ζ)
  rw [one_mul] at hlim
  have htarget : (∫ ζ, φh ζ * D ζ) / ∫ ζ, D ζ = ballExpectation r Ψ φ := by
    unfold ballExpectation
    congr 1
    apply integral_congr_ae
    filter_upwards with ζ
    exact hφD ζ
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one (α := ℝ))] with t ht
  unfold ballExpectation
  rw [hchange t ht.1 ht.2.le]
theorem exists_contDiff_extension_smul {ρ t : ℝ} (hρ : 0 < ρ) (ht0 : 0 < t) (ht1 : t < 1)
    {f : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f {η | ∀ b, ‖η b‖ < ρ}) :
    ∃ F : BondField ι → ℝ, ContDiff ℝ 1 F ∧ ∀ η, (∀ b, ‖η b‖ < ρ) →
      F η = f (t • η) ∧ ∀ b, bondGradNorm F b η = t * bondGradNorm f b (t • η) := by
  classical
  have hρt : ρ < ρ / t := by
    rw [lt_div_iff₀ ht0]
    nlinarith
  set s := ρ / t - ρ with hs
  let β : ContDiffBump (0 : BondField ι) :=
    ⟨ρ + s / 3, ρ + 2 * s / 3, by positivity, by linarith⟩
  set F : BondField ι → ℝ := fun η => if ‖η‖ < ρ / t then β η * f (t • η) else 0 with hF
  have hcomp : ContDiffOn ℝ 1 (fun η : BondField ι => f (t • η)) (Metric.ball 0 (ρ / t)) := by
    refine hf.comp (contDiff_const_smul t).contDiffOn ?_
    intro η hη b
    have h1 : ‖η‖ < ρ / t := mem_ball_zero_iff.mp hη
    have h2 : ‖η b‖ ≤ ‖η‖ := norm_le_pi_norm η b
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg ht0.le]
    have h3 : ‖η b‖ < ρ / t := lt_of_le_of_lt h2 h1
    rw [lt_div_iff₀ ht0] at h3
    linarith
  have hopen : IsOpen (Metric.ball (0 : BondField ι) (ρ / t)) := Metric.isOpen_ball
  have hFc : ContDiff ℝ 1 F := by
    rw [contDiff_iff_contDiffAt]
    intro η
    by_cases h : ‖η‖ < ρ / t
    · have hmem : η ∈ Metric.ball (0 : BondField ι) (ρ / t) := mem_ball_zero_iff.mpr h
      have h1 : ContDiffAt ℝ 1 (fun ζ => β ζ * f (t • ζ)) η :=
        (β.contDiff.contDiffAt).mul (hcomp.contDiffAt (hopen.mem_nhds hmem))
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hmem] with ζ hζ
      simp only [hF, if_pos (mem_ball_zero_iff.mp hζ)]
    · have hfar : ρ + 2 * s / 3 < ‖η‖ := by
        have : ρ / t ≤ ‖η‖ := not_lt.mp h
        linarith
      have hnear : ∀ᶠ ζ in 𝓝 η, ρ + 2 * s / 3 < ‖ζ‖ :=
        (continuous_norm.tendsto η).eventually (lt_mem_nhds hfar)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hnear] with ζ hζ
      simp only [hF]
      split_ifs
      · have : β ζ = 0 := by
          apply β.zero_of_le_dist
          rw [dist_zero_right]
          exact hζ.le
        rw [this, zero_mul]
      · rfl
  refine ⟨F, hFc, ?_⟩
  intro η hη
  have hOo : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := isOpen_setOf_norm_lt hρ
  have heq : ∀ ζ, (∀ b, ‖ζ b‖ < ρ) → F ζ = f (t • ζ) := by
    intro ζ hζ
    have hb : ‖ζ‖ < ρ := (pi_norm_lt_iff hρ).mpr hζ
    have hlt : ‖ζ‖ < ρ / t := hb.trans hρt
    have h1 : β ζ = 1 := by
      apply β.one_of_mem_closedBall
      rw [mem_closedBall_zero_iff]
      change ‖ζ‖ ≤ ρ + s / 3
      linarith
    simp only [hF, if_pos hlt, h1, one_mul]
  refine ⟨heq η hη, fun b => ?_⟩
  have hev : F =ᶠ[𝓝 η] fun ζ => f (t • ζ) := by
    filter_upwards [hOo.mem_nhds hη] with ζ hζ
    exact heq ζ hζ
  have hin : t • η ∈ {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    intro b
    have h1 := hη b
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg ht0.le]
    nlinarith [norm_nonneg (η b)]
  unfold bondGradNorm
  rw [hev.fderiv_eq, fderiv_comp_smul, ContinuousLinearMap.smul_comp, norm_smul,
    Real.norm_of_nonneg ht0.le]
theorem continuousOn_bondGradNorm {ρ : ℝ} (hρ : 0 < ρ) {f : BondField ι → ℝ}
    (hf : ContDiffOn ℝ 1 f {η | ∀ b, ‖η b‖ < ρ}) (b : ι) :
    ContinuousOn (bondGradNorm f b) {η | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.continuousOn_bondGradNorm <;> assumption
theorem covarianceOpenBalls (hCov : BallCovarianceBound)
    (hLaw : normalizedBallLawIsProbabilityStatement) : covarianceOpenBallsStatement := by
  intro ι _ _ ρ m κ d Ψ K p hρ hm hκ hcut hd hconv f g hf hg hf2 hg2 hdf hdg
  have hΨ : Continuous Ψ := hconv.smooth.continuous
  obtain ⟨hprob, hmean, hiff, hae, hmeas, hnn, hint, hZ, hcont, hsupp, hanti⟩ :=
    hLaw ι ρ p Ψ hρ hcut hΨ
  set r := cutoffFactor ρ p with hr
  set O : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hO
  set ν := normalizedBallLaw r Ψ with hν
  have hs : ∀ η, ballDensity r Ψ η ≠ 0 → ∀ b, ‖η b‖ < ρ := fun η h => (hsupp η).mp h
  have hOo : IsOpen O := isOpen_setOf_norm_lt hρ
  have haes : ∀ {φ : BondField ι → ℝ}, ContinuousOn φ O → AEStronglyMeasurable φ ν := by
    intro φ hφ
    classical
    have hm' : Measurable (O.indicator φ) := by
      rw [← Set.piecewise_eq_indicator]
      exact ContinuousOn.measurable_piecewise hφ continuous_const.continuousOn hOo.measurableSet
    refine hm'.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with η hη
    exact Set.indicator_of_mem (show η ∈ O from hη) φ
  have hfc : ContinuousOn f O := hf.continuousOn
  have hgc : ContinuousOn g O := hg.continuousOn
  have hone : Integrable (fun _ : BondField ι => (1 : ℝ)) ν := integrable_const _
  have hf1 : Integrable f ν := by
    refine Integrable.mono' (hone.add hf2) (haes hfc) (ae_of_all _ fun η => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [sq_abs (f η), sq_nonneg (|f η| - 1)]
  have hg1 : Integrable g ν := by
    refine Integrable.mono' (hone.add hg2) (haes hgc) (ae_of_all _ fun η => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [sq_abs (g η), sq_nonneg (|g η| - 1)]
  have hfg : Integrable (fun η => f η * g η) ν := by
    refine Integrable.mono' (hf2.add hg2) (haes (hfc.mul hgc)) (ae_of_all _ fun η => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    simp only [Pi.add_apply]
    nlinarith [sq_abs (f η), sq_abs (g η), sq_nonneg (|f η| - |g η|), abs_nonneg (f η),
      abs_nonneg (g η)]
  obtain ⟨B, hB⟩ : ∃ B, ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → |Ψ η| ≤ B := by
    have hK : IsCompact {η : BondField ι | ∀ b, ‖η b‖ ≤ ρ} := by
      have : {η : BondField ι | ∀ b, ‖η b‖ ≤ ρ} =
          Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : BondVector) ρ := by
        ext η
        simp [Set.mem_pi]
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hΨ.continuousOn
    exact ⟨B, fun η h => hB η h⟩
  have hdom : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ ζ,
      ballDensity r Ψ (t⁻¹ • ζ) ≤ Real.exp (2 * B) * ballDensity r Ψ ζ := by
    intro t ht ht1 ζ
    by_cases hz : ballDensity r Ψ (t⁻¹ • ζ) = 0
    · rw [hz]
      exact mul_nonneg (Real.exp_pos _).le (hnn ζ)
    have hin := hs _ hz
    have hle : ∀ b, ‖ζ b‖ ≤ ‖(t⁻¹ • ζ) b‖ := by
      intro b
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le]
      have h1 : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
      nlinarith [norm_nonneg (ζ b)]
    have hζ : ∀ b, ‖ζ b‖ < ρ := fun b => lt_of_le_of_lt (hle b) (hin b)
    have h1 : ∏ b, r ‖(t⁻¹ • ζ) b‖ ≤ ∏ b, r ‖ζ b‖ := by
      apply Finset.prod_le_prod
      · intro b _
        simp only [hr, cutoffFactor]
        split_ifs
        · exact (Real.exp_pos _).le
        · exact le_rfl
      · intro b _
        exact hanti _ _ (norm_nonneg _) (hle b)
    have hb1 := hB (t⁻¹ • ζ) fun b => (hin b).le
    have hb2 := hB ζ fun b => (hζ b).le
    have h2 : Real.exp (-Ψ (t⁻¹ • ζ)) ≤ Real.exp (2 * B) * Real.exp (-Ψ ζ) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := abs_le.mp hb1
      have := abs_le.mp hb2
      linarith
    have hr0 : 0 ≤ ∏ b, r ‖ζ b‖ := by
      apply Finset.prod_nonneg
      intro b _
      simp only [hr, cutoffFactor]
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    have hr1 : 0 ≤ ∏ b, r ‖(t⁻¹ • ζ) b‖ := by
      apply Finset.prod_nonneg
      intro b _
      simp only [hr, cutoffFactor]
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    change (∏ b, r ‖(t⁻¹ • ζ) b‖) * Real.exp (-Ψ (t⁻¹ • ζ)) ≤
      Real.exp (2 * B) * ((∏ b, r ‖ζ b‖) * Real.exp (-Ψ ζ))
    calc (∏ b, r ‖(t⁻¹ • ζ) b‖) * Real.exp (-Ψ (t⁻¹ • ζ))
        ≤ (∏ b, r ‖ζ b‖) * (Real.exp (2 * B) * Real.exp (-Ψ ζ)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le hr0
      _ = _ := by ring
  have hlim : ∀ {φ : BondField ι → ℝ}, ContinuousOn φ O → Integrable φ ν →
      Tendsto (fun t : ℝ => ballExpectation r Ψ fun η => φ (t • η)) (𝓝[<] 1)
        (𝓝 (ballExpectation r Ψ φ)) :=
    fun hφ hi => tendsto_ballExpectation_smul hρ hmeas hcont hs _ hdom hnn hφ ((hiff _).mp hi)
  have hcf : ∀ b, ContinuousOn (fun η => bondGradNorm f b η ^ 2) O := fun b =>
    (continuousOn_bondGradNorm hρ hf b).pow 2
  have hcg : ∀ b, ContinuousOn (fun η => bondGradNorm g b η ^ 2) O := fun b =>
    (continuousOn_bondGradNorm hρ hg b).pow 2
  have hat : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      |(ballExpectation r Ψ fun η => f (t • η) * g (t • η)) -
          (ballExpectation r Ψ fun η => f (t • η)) * ballExpectation r Ψ fun η => g (t • η)| ≤
        m⁻¹ * ∑ b, ∑ b',
          Real.sqrt (t ^ 2 * ballExpectation r Ψ fun η => bondGradNorm f b (t • η) ^ 2) *
            Real.exp (-(κ * d b b')) *
          Real.sqrt (t ^ 2 * ballExpectation r Ψ fun η => bondGradNorm g b' (t • η) ^ 2) := by
    intro t ht
    obtain ⟨Ff, hFf, hFf'⟩ := exists_contDiff_extension_smul hρ ht.1 ht.2 hf
    obtain ⟨Fg, hFg, hFg'⟩ := exists_contDiff_extension_smul hρ ht.1 ht.2 hg
    have h := hCov ι ρ m κ d Ψ K p hρ hm hκ hcut hd hconv Ff Fg hFf hFg
    have e1 : ballExpectation r Ψ (fun η => Ff η * Fg η) =
        ballExpectation r Ψ fun η => f (t • η) * g (t • η) :=
      ballExpectation_congr hs fun η hη => by rw [(hFf' η hη).1, (hFg' η hη).1]
    have e2 : ballExpectation r Ψ Ff = ballExpectation r Ψ fun η => f (t • η) :=
      ballExpectation_congr hs fun η hη => (hFf' η hη).1
    have e3 : ballExpectation r Ψ Fg = ballExpectation r Ψ fun η => g (t • η) :=
      ballExpectation_congr hs fun η hη => (hFg' η hη).1
    have e4 : ∀ b, ballL2Norm r Ψ (bondGradNorm Ff b) =
        Real.sqrt (t ^ 2 * ballExpectation r Ψ fun η => bondGradNorm f b (t • η) ^ 2) := by
      intro b
      unfold ballL2Norm
      rw [← ballExpectation_const_mul]
      congr 1
      refine ballExpectation_congr hs fun η hη => ?_
      rw [(hFf' η hη).2 b]
      ring
    have e5 : ∀ b, ballL2Norm r Ψ (bondGradNorm Fg b) =
        Real.sqrt (t ^ 2 * ballExpectation r Ψ fun η => bondGradNorm g b (t • η) ^ 2) := by
      intro b
      unfold ballL2Norm
      rw [← ballExpectation_const_mul]
      congr 1
      refine ballExpectation_congr hs fun η hη => ?_
      rw [(hFg' η hη).2 b]
      ring
    have h' : |ballCovariance r Ψ Ff Fg| ≤ m⁻¹ * ∑ b, ∑ b', ballL2Norm r Ψ (bondGradNorm Ff b) *
        Real.exp (-(κ * d b b')) * ballL2Norm r Ψ (bondGradNorm Fg b') := h
    simp only [ballCovariance, e1, e2, e3, e4, e5] at h'
    exact h'
  have hL : Tendsto (fun t : ℝ => |(ballExpectation r Ψ fun η => f (t • η) * g (t • η)) -
      (ballExpectation r Ψ fun η => f (t • η)) * ballExpectation r Ψ fun η => g (t • η)|) (𝓝[<] 1)
      (𝓝 |ballCovariance r Ψ f g|) := by
    unfold ballCovariance
    exact ((hlim (hfc.mul hgc) hfg).sub ((hlim hfc hf1).mul (hlim hgc hg1))).abs
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (𝓝[<] 1) (𝓝 1) := by
    have h := (continuous_pow 2 : Continuous fun t : ℝ => t ^ 2).tendsto 1
    simp only [one_pow] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hnf : ∀ b, Tendsto (fun t : ℝ =>
      Real.sqrt (t ^ 2 * ballExpectation r Ψ fun η => bondGradNorm f b (t • η) ^ 2)) (𝓝[<] 1)
      (𝓝 (ballL2Norm r Ψ (bondGradNorm f b))) := by
    intro b
    have h := (hsq.mul (hlim (hcf b) (hdf b))).sqrt
    rw [one_mul] at h
    exact h
  have hng : ∀ b, Tendsto (fun t : ℝ =>
      Real.sqrt (t ^ 2 * ballExpectation r Ψ fun η => bondGradNorm g b (t • η) ^ 2)) (𝓝[<] 1)
      (𝓝 (ballL2Norm r Ψ (bondGradNorm g b))) := by
    intro b
    have h := (hsq.mul (hlim (hcg b) (hdg b))).sqrt
    rw [one_mul] at h
    exact h
  have hR : Tendsto (fun t : ℝ => m⁻¹ * ∑ b, ∑ b',
      Real.sqrt (t ^ 2 * ballExpectation r Ψ fun η => bondGradNorm f b (t • η) ^ 2) *
        Real.exp (-(κ * d b b')) *
      Real.sqrt (t ^ 2 * ballExpectation r Ψ fun η => bondGradNorm g b' (t • η) ^ 2)) (𝓝[<] 1)
      (𝓝 (m⁻¹ * ∑ b, ∑ b', ballL2Norm r Ψ (bondGradNorm f b) * Real.exp (-(κ * d b b')) *
        ballL2Norm r Ψ (bondGradNorm g b'))) := by
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro b _
    apply tendsto_finsetSum
    intro b' _
    exact ((hnf b).mul_const _).mul (hng b')
  refine le_of_tendsto_of_tendsto hL hR ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one (α := ℝ))] with t ht
  exact hat t ht
end ConvexObservables.OpenBallCovariance
end YangMills.Construction
end
