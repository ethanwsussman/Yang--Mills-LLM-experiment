import YangMills.Construction.ClusterExpansionOfAStep.SecondMomentOfAConvexLawProof
import YangMills.Construction.ColdStepAtMirrorFrames.MomentsOfAConvexMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace BallMoments
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem hasDerivAt_lineRestriction {G : BondField ι → ℝ} (hG : Differentiable ℝ G) (η u : BondField ι) :
    HasDerivAt (fun s : ℝ => G (η + s • u)) (fderiv ℝ G η u) 0 := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.hasDerivAt_fderiv_line <;> assumption
theorem radialWeightProd_nonneg {ρ : ℝ} {r : ℝ → ℝ} (hr : IsRadialCutoff ρ r) (η : BondField ι) :
    0 ≤ radialWeightProd r η := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.radialWeightProd_nonneg <;> assumption
theorem norm_lt_of_radialWeightProd_ne_zero {ρ : ℝ} {r : ℝ → ℝ} (hr : IsRadialCutoff ρ r) (η : BondField ι)
    (h : radialWeightProd r η ≠ 0) (b : ι) : ‖η b‖ < ρ := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.norm_lt_of_radialWeightProd_ne_zero <;> assumption
theorem fderiv_radialWeightProd_single_nonpos {ρ : ℝ} {r : ℝ → ℝ} (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r)
    (η : BondField ι) (b : ι) :
    fderiv ℝ (radialWeightProd (ι := ι) r) η (Pi.single b (η b) : BondField ι) ≤ 0 := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.fderiv_radialWeightProd_dilation_nonpos <;> assumption
theorem contDiff_ballDensity {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ r) (hΨ : ContDiff ℝ 3 Ψ) : ContDiff ℝ 1 (ballDensity r Ψ) := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.contDiff_ballDensity <;> assumption
theorem hasCompactSupport_ballDensity {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ r) : HasCompactSupport (ballDensity r Ψ) := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.hasCompactSupport_ballDensity <;> assumption
theorem ballDensity_nonneg {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hr : IsRadialCutoff ρ r)
    (η : BondField ι) : 0 ≤ ballDensity r Ψ η :=
  mul_nonneg (radialWeightProd_nonneg hr η) (Real.exp_pos _).le
theorem integrable_mul_of_hasCompactSupport {ϱ g : BondField ι → ℝ} (hϱ : Continuous ϱ)
    (hc : HasCompactSupport ϱ) (hg : Continuous g) : Integrable (fun η => g η * ϱ η) := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.integrable_mul_of_hasCompactSupport <;> assumption
def bondDilation (b : ι) (η : BondField ι) : BondField ι := Pi.single b (η b)
theorem continuous_bondDilation (b : ι) : Continuous (bondDilation (ι := ι) b) := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.continuous_bondDilation <;> assumption
theorem integral_mul_fderiv_bondDilation {T ϱ : BondField ι → ℝ} (hT : ContDiff ℝ 1 T) (hϱ : ContDiff ℝ 1 ϱ)
    (hc : HasCompactSupport ϱ) (b : ι) :
    ∫ η, T η * fderiv ℝ ϱ η (bondDilation b η) =
      - ∫ η, (fderiv ℝ T η (bondDilation b η) + 3 * T η) * ϱ η := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.integral_mul_fderiv_bondDilation <;> assumption
theorem fderiv_ballDensity {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ r) (hΨ : ContDiff ℝ 3 Ψ) (η u : BondField ι) :
    fderiv ℝ (ballDensity r Ψ) η u = Real.exp (- Ψ η) * fderiv ℝ (radialWeightProd r) η u -
      ballDensity r Ψ η * fderiv ℝ Ψ η u := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.fderiv_ballDensity <;> assumption
theorem weighted_hessian_lower_bound {ρ m κ : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
    (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hd : IsPseudoMetricOnBonds d) (hC : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (b₀ : ι) (ζ η : BondField ι) (hζ : ∀ b, ‖ζ b‖ < ρ) :
    m * ∑ b, Real.exp (-(2 * κ * d b b₀)) * ‖η b‖ ^ 2 ≤
      ∑ b, Real.exp (-(2 * κ * d b b₀)) * secondDerivAlong Ψ ζ (Pi.single b (η b)) η := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.weighted_hessian_lower_bound <;> assumption
theorem weighted_dilation_slope_lower_bound {ρ m κ W : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ}
    {K : ι → ι → ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hκ : 0 ≤ κ) (hd : IsPseudoMetricOnBonds d)
    (hC : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (hW : ∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W)
    (hs : ∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt m * ‖e‖) (b₀ : ι)
    (η : BondField ι) (hη : ∀ b, ‖η b‖ < ρ) :
    m / 2 * (∑ b, Real.exp (-(2 * κ * d b b₀)) * ‖η b‖ ^ 2) - W / 2 ≤
      ∑ b, Real.exp (-(2 * κ * d b b₀)) * fderiv ℝ Ψ η (bondDilation b η) := by
  set w : ι → ℝ := fun b => Real.exp (-(2 * κ * d b b₀)) with hw
  have hw0 : ∀ b, 0 < w b := fun b => Real.exp_pos _
  have hdiff2 : ∀ u : BondField ι, Differentiable ℝ fun ζ => fderiv ℝ Ψ ζ u := by
    intro u
    have h2 : Differentiable ℝ (fderiv ℝ Ψ) :=
      (hC.smooth.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
    exact fun ζ => ((h2 ζ).hasFDerivAt.clm_apply (hasFDerivAt_const u ζ)).differentiableAt
  set h : ℝ → ℝ := fun s => ∑ b, w b * fderiv ℝ Ψ (s • η) (bondDilation b η) with hh
  set h' : ℝ → ℝ := fun s => ∑ b, w b * secondDerivAlong Ψ (s • η) (bondDilation b η) η with hh'
  have hder : ∀ s, HasDerivAt h (h' s) s := by
    intro s
    apply HasDerivAt.fun_sum
    intro b _
    apply HasDerivAt.const_mul
    have h1 : HasDerivAt (fun s : ℝ => s • η) η s := by
      simpa using (hasDerivAt_id s).smul_const η
    exact ((hdiff2 (bondDilation b η) (s • η)).hasFDerivAt).comp_hasDerivAt s h1
  obtain ⟨θ, hθ, hmv⟩ := exists_hasDerivAt_eq_slope h h' (zero_lt_one)
    (continuous_iff_continuousAt.mpr fun s => (hder s).continuousAt).continuousOn
    (fun s _ => hder s)
  have hθη : ∀ b, ‖(θ • η) b‖ < ρ := by
    intro b
    have : (θ • η) b = θ • η b := rfl
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hθ.1]
    have h1 := hη b
    have h2 := norm_nonneg (η b)
    nlinarith [hθ.2]
  have hfl := weighted_hessian_lower_bound hρ hκ hd hC b₀ (θ • η) η hθη
  have e1 : h 1 = ∑ b, w b * fderiv ℝ Ψ η (bondDilation b η) := by
    simp only [hh, one_smul]
  have e0 : h 0 = ∑ b, w b * bondPartialDeriv Ψ b 0 (η b) := by
    simp only [hh, zero_smul]
    rfl
  have hh0 : -(Real.sqrt m * ∑ b, w b * ‖η b‖) ≤ h 0 := by
    rw [e0, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro b _
    have h1 := hs b (η b)
    have h2 := neg_abs_le (bondPartialDeriv Ψ b 0 (η b))
    have h3 := hw0 b
    nlinarith
  have hsq : Real.sqrt m * ∑ b, w b * ‖η b‖ ≤ m / 2 * (∑ b, w b * ‖η b‖ ^ 2) + W / 2 := by
    have hsm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
    have h1 : ∀ b, Real.sqrt m * (w b * ‖η b‖) ≤ m / 2 * (w b * ‖η b‖ ^ 2) + w b / 2 := by
      intro b
      have h2 := hw0 b
      have h3 : 0 ≤ (Real.sqrt m * ‖η b‖ - 1) ^ 2 := sq_nonneg _
      have e : (Real.sqrt m * ‖η b‖ - 1) ^ 2 = m * ‖η b‖ ^ 2 - 2 * (Real.sqrt m * ‖η b‖) + 1 := by
        rw [sub_sq, mul_pow, hsm]
        ring
      rw [e] at h3
      have h4 := mul_nonneg h2.le h3
      nlinarith [h4]
    calc Real.sqrt m * ∑ b, w b * ‖η b‖ = ∑ b, Real.sqrt m * (w b * ‖η b‖) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ b, (m / 2 * (w b * ‖η b‖ ^ 2) + w b / 2) := Finset.sum_le_sum fun b _ => h1 b
      _ = m / 2 * (∑ b, w b * ‖η b‖ ^ 2) + (∑ b, w b) / 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
      _ ≤ m / 2 * (∑ b, w b * ‖η b‖ ^ 2) + W / 2 := by
          have := hW b₀
          linarith
  have e3 : m * (∑ b, w b * ‖η b‖ ^ 2) ≤ h' θ := hfl
  rw [← e1]
  linarith
def weightedSquare (w : ι → ℝ) (η : BondField ι) : ℝ := ∑ b, w b * ‖η b‖ ^ 2
theorem contDiff_weightedSquare (w : ι → ℝ) : ContDiff ℝ 1 (weightedSquare w) := by
  unfold weightedSquare
  apply ContDiff.sum
  intro b _
  exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ BondVector b))
theorem weightedSquare_add_smul_bondDilation (w : ι → ℝ) (η : BondField ι) (b : ι) (s : ℝ) :
    weightedSquare w (η + s • bondDilation b η) =
      weightedSquare w η + w b * ((1 + s) ^ 2 - 1) * ‖η b‖ ^ 2 := by
  unfold weightedSquare
  have h : ∀ b', w b' * ‖(η + s • bondDilation b η) b'‖ ^ 2 =
      w b' * ‖η b'‖ ^ 2 + if b' = b then w b * ((1 + s) ^ 2 - 1) * ‖η b‖ ^ 2 else 0 := by
    intro b'
    by_cases hb : b' = b
    · subst hb
      have e : (η + s • bondDilation b' η) b' = (1 + s) • η b' := by
        simp [bondDilation, add_smul]
      rw [e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, if_pos rfl]
      ring
    · have e : (η + s • bondDilation b η) b' = η b' := by
        simp [bondDilation, Pi.single_eq_of_ne hb]
      rw [e, if_neg hb, add_zero]
  simp only [h]
  rw [Finset.sum_add_distrib]
  simp
theorem fderiv_weightedSquare_bondDilation (w : ι → ℝ) (η : BondField ι) (b : ι) :
    fderiv ℝ (weightedSquare w) η (bondDilation b η) = 2 * w b * ‖η b‖ ^ 2 := by
  have hl := hasDerivAt_lineRestriction ((contDiff_weightedSquare w).differentiable (by norm_num)) η
    (bondDilation b η)
  have h2 : HasDerivAt (fun s : ℝ => weightedSquare w η + w b * ((1 + s) ^ 2 - 1) * ‖η b‖ ^ 2)
      (2 * w b * ‖η b‖ ^ 2) 0 := by
    have h3 : HasDerivAt (fun s : ℝ => (1 + s) ^ 2 - 1) 2 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_add 1).fun_pow 2).sub_const 1
      refine HasDerivAt.congr_deriv this ?_
      simp
    exact HasDerivAt.congr_deriv (((h3.const_mul (w b)).mul_const (‖η b‖ ^ 2)).const_add _)
      (by ring)
  have e : (fun s : ℝ => weightedSquare w (η + s • bondDilation b η)) =
      fun s : ℝ => weightedSquare w η + w b * ((1 + s) ^ 2 - 1) * ‖η b‖ ^ 2 :=
    funext fun s => weightedSquare_add_smul_bondDilation w η b s
  rw [e] at hl
  exact hl.unique h2
theorem fderiv_const_mul_weightedSquare_pow (w : ι → ℝ) (c : ℝ) (q : ℕ) (η : BondField ι) (b : ι) :
    fderiv ℝ (fun ζ => c * weightedSquare w ζ ^ q) η (bondDilation b η) =
      c * (q * weightedSquare w η ^ (q - 1) * (2 * w b * ‖η b‖ ^ 2)) := by
  have hd : Differentiable ℝ (fun ζ => c * weightedSquare w ζ ^ q) :=
    (contDiff_const.mul ((contDiff_weightedSquare w).pow q)).differentiable (by norm_num)
  have hl := hasDerivAt_lineRestriction hd η (bondDilation b η)
  have hY := hasDerivAt_lineRestriction ((contDiff_weightedSquare w).differentiable (by norm_num)) η
    (bondDilation b η)
  rw [fderiv_weightedSquare_bondDilation] at hY
  have h2 := (hY.fun_pow q).const_mul c
  have h3 := hl.unique h2
  rw [h3]
  simp
theorem weightedSquare_moment_step {ρ m κ W : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
    {r : ℝ → ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hκ : 0 ≤ κ) (hr : IsRadialCutoff ρ r)
    (hd : IsPseudoMetricOnBonds d) (hC : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (hW : ∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W)
    (hs : ∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt m * ‖e‖) (b₀ : ι) (q : ℕ) :
    m / 2 * ∫ η, weightedSquare (fun b => Real.exp (-(2 * κ * d b b₀))) η ^ (q + 1) * ballDensity r Ψ η ≤
      (2 * q + 4 * W) * ∫ η, weightedSquare (fun b => Real.exp (-(2 * κ * d b b₀))) η ^ q *
        ballDensity r Ψ η := by
  set w : ι → ℝ := fun b => Real.exp (-(2 * κ * d b b₀)) with hw
  set Y := weightedSquare w with hY
  set ϱ := ballDensity r Ψ with hϱd
  have hϱ : ContDiff ℝ 1 ϱ := contDiff_ballDensity hρ hr hC.smooth
  have hc : HasCompactSupport ϱ := hasCompactSupport_ballDensity hρ hr
  have hϱc : Continuous ϱ := hϱ.continuous
  have hϱ0 : ∀ η, 0 ≤ ϱ η := fun η => ballDensity_nonneg hr η
  have hw0 : ∀ b, 0 < w b := fun b => Real.exp_pos _
  have hdnn : ∀ b b', 0 ≤ d b b' := by
    intro b b'
    have h1 := hd.triangle b b' b
    rw [hd.self, hd.symm b' b] at h1
    linarith
  have hw1 : ∀ b, w b ≤ 1 := by
    intro b
    apply Real.exp_le_one_iff.mpr
    have := mul_nonneg hκ (hdnn b b₀)
    linarith
  have hWsum : ∑ b, w b ≤ W := hW b₀
  have hW0 : 0 ≤ W := (Finset.sum_nonneg fun b _ => (hw0 b).le).trans hWsum
  have hY0 : ∀ η, 0 ≤ Y η := fun η => Finset.sum_nonneg fun b _ => by
    have := hw0 b
    positivity
  have hYc : ContDiff ℝ 1 Y := contDiff_weightedSquare w
  set T : ι → BondField ι → ℝ := fun b η => w b * Y η ^ q with hT
  have hTs : ∀ b, ContDiff ℝ 1 (T b) := fun b => contDiff_const.mul (hYc.pow q)
  have hT0 : ∀ b η, 0 ≤ T b η := fun b η => mul_nonneg (hw0 b).le (pow_nonneg (hY0 η) _)
  have hdc : ∀ (G : BondField ι → ℝ), ContDiff ℝ 1 G → ∀ b,
      Continuous fun η => fderiv ℝ G η (bondDilation b η) := fun G hG b =>
    (hG.continuous_fderiv (by norm_num)).clm_apply (continuous_bondDilation b)
  have hΨ1 : ContDiff ℝ 1 Ψ := hC.smooth.of_le (by norm_num)
  have hb : ∀ b, ∫ η, (T b η * fderiv ℝ Ψ η (bondDilation b η)) * ϱ η ≤
      ∫ η, (fderiv ℝ (T b) η (bondDilation b η) + 3 * T b η) * ϱ η := by
    intro b
    have hbp := integral_mul_fderiv_bondDilation (hTs b) hϱ hc b
    have i1 : Integrable fun η => T b η * fderiv ℝ ϱ η (bondDilation b η) := by
      refine Continuous.integrable_of_hasCompactSupport
        ((hTs b).continuous.mul (hdc ϱ hϱ b)) ?_
      refine (hc.fderiv (𝕜 := ℝ)).mono ?_
      intro η hη
      simp only [Function.mem_support] at hη ⊢
      intro h0
      apply hη
      simp [h0]
    have i2 : Integrable fun η => -((T b η * fderiv ℝ Ψ η (bondDilation b η)) * ϱ η) :=
      (integrable_mul_of_hasCompactSupport hϱc hc ((hTs b).continuous.mul (hdc Ψ hΨ1 b))).neg
    have hle : ∫ η, T b η * fderiv ℝ ϱ η (bondDilation b η) ≤
        ∫ η, -((T b η * fderiv ℝ Ψ η (bondDilation b η)) * ϱ η) := by
      apply integral_mono i1 i2
      intro η
      have hs1 := fderiv_ballDensity hρ hr hC.smooth η (bondDilation b η)
      have hs2 := fderiv_radialWeightProd_single_nonpos (ι := ι) hρ hr η b
      have hE := Real.exp_pos (- Ψ η)
      simp only []
      rw [hs1]
      have h1 : T b η * (Real.exp (- Ψ η) * fderiv ℝ (radialWeightProd r) η (bondDilation b η)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hT0 b η)
          (mul_nonpos_of_nonneg_of_nonpos hE.le hs2)
      have e : T b η * (Real.exp (- Ψ η) * fderiv ℝ (radialWeightProd r) η (bondDilation b η) -
          ballDensity r Ψ η * fderiv ℝ Ψ η (bondDilation b η)) =
          T b η * (Real.exp (- Ψ η) * fderiv ℝ (radialWeightProd r) η (bondDilation b η)) +
            -(T b η * fderiv ℝ Ψ η (bondDilation b η) * ϱ η) := by
        simp only [hϱd]
        ring
      rw [e]
      linarith
    rw [integral_neg, hbp] at hle
    linarith
  have hIint : ∀ b, Integrable fun η => (T b η * fderiv ℝ Ψ η (bondDilation b η)) * ϱ η := fun b =>
    integrable_mul_of_hasCompactSupport hϱc hc ((hTs b).continuous.mul (hdc Ψ hΨ1 b))
  have hJint : ∀ b, Integrable fun η =>
      (fderiv ℝ (T b) η (bondDilation b η) + 3 * T b η) * ϱ η := fun b =>
    integrable_mul_of_hasCompactSupport hϱc hc
      ((hdc _ (hTs b) b).add (continuous_const.mul (hTs b).continuous))
  have hsum : ∫ η, ∑ b, (T b η * fderiv ℝ Ψ η (bondDilation b η)) * ϱ η ≤
      ∫ η, ∑ b, (fderiv ℝ (T b) η (bondDilation b η) + 3 * T b η) * ϱ η := by
    rw [integral_finset_sum _ fun b _ => hIint b, integral_finset_sum _ fun b _ => hJint b]
    exact Finset.sum_le_sum fun b _ => hb b
  have hYcon : Continuous Y := hYc.continuous
  have iq : Integrable fun η => Y η ^ q * ϱ η :=
    integrable_mul_of_hasCompactSupport hϱc hc (hYcon.pow q)
  have iq1 : Integrable fun η => Y η ^ (q + 1) * ϱ η :=
    integrable_mul_of_hasCompactSupport hϱc hc (hYcon.pow (q + 1))
  have hlow : ∫ η, (m / 2 * Y η ^ (q + 1) - W / 2 * Y η ^ q) * ϱ η ≤
      ∫ η, ∑ b, (T b η * fderiv ℝ Ψ η (bondDilation b η)) * ϱ η := by
    apply integral_mono
    · exact integrable_mul_of_hasCompactSupport hϱc hc
        ((continuous_const.mul (hYcon.pow _)).sub (continuous_const.mul (hYcon.pow _)))
    · exact integrable_finset_sum _ fun b _ => hIint b
    · intro η
      simp only []
      rw [← Finset.sum_mul]
      by_cases h0 : ϱ η = 0
      · simp [h0]
      · apply mul_le_mul_of_nonneg_right _ (hϱ0 η)
        have hR : radialWeightProd r η ≠ 0 := fun h => h0 (by simp [hϱd, ballDensity, h])
        have hin := norm_lt_of_radialWeightProd_ne_zero hr η hR
        have hws := weighted_dilation_slope_lower_bound hρ hm hκ hd hC hW hs b₀ η hin
        have e : ∑ b, T b η * fderiv ℝ Ψ η (bondDilation b η) =
            Y η ^ q * ∑ b, w b * fderiv ℝ Ψ η (bondDilation b η) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          simp only [hT]
          ring
        rw [e]
        have hp := pow_nonneg (hY0 η) q
        have e2 : m / 2 * Y η ^ (q + 1) - W / 2 * Y η ^ q = Y η ^ q * (m / 2 * Y η - W / 2) := by
          rw [pow_succ]
          ring
        rw [e2]
        exact mul_le_mul_of_nonneg_left hws hp
  have hup : ∫ η, ∑ b, (fderiv ℝ (T b) η (bondDilation b η) + 3 * T b η) * ϱ η ≤
      ∫ η, ((2 * q + 3 * W) * Y η ^ q) * ϱ η := by
    apply integral_mono
    · exact integrable_finset_sum _ fun b _ => hJint b
    · exact integrable_mul_of_hasCompactSupport hϱc hc (continuous_const.mul (hYcon.pow _))
    · intro η
      simp only []
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (hϱ0 η)
      have e1 : ∀ b, fderiv ℝ (T b) η (bondDilation b η) + 3 * T b η =
          (q * Y η ^ (q - 1) * 2) * (w b * (w b * ‖η b‖ ^ 2)) + 3 * w b * Y η ^ q := by
        intro b
        have := fderiv_const_mul_weightedSquare_pow w (w b) q η b
        simp only [hT]
        rw [show (fun η => w b * Y η ^ q) = fun ζ => w b * weightedSquare w ζ ^ q from rfl, this]
        ring
      simp only [e1]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
      have h1 : ∑ b, w b * (w b * ‖η b‖ ^ 2) ≤ Y η := by
        apply Finset.sum_le_sum
        intro b _
        have h2 := hw1 b
        have h4 : 0 ≤ w b * ‖η b‖ ^ 2 := by positivity
        nlinarith
      have h5 : q * Y η ^ (q - 1) * 2 * ∑ b, w b * (w b * ‖η b‖ ^ 2) ≤ 2 * q * Y η ^ q := by
        rcases Nat.eq_zero_or_pos q with rfl | hq
        · simp
        · have e3 : Y η ^ q = Y η ^ (q - 1) * Y η := by
            rw [← pow_succ, Nat.sub_add_cancel hq]
          rw [e3]
          have hnn : 0 ≤ (q : ℝ) * Y η ^ (q - 1) * 2 := by
            have := pow_nonneg (hY0 η) (q - 1)
            positivity
          calc q * Y η ^ (q - 1) * 2 * ∑ b, w b * (w b * ‖η b‖ ^ 2)
              ≤ q * Y η ^ (q - 1) * 2 * Y η := mul_le_mul_of_nonneg_left h1 hnn
            _ = 2 * q * (Y η ^ (q - 1) * Y η) := by ring
      have h6 : 3 * (∑ b, w b) * Y η ^ q ≤ 3 * W * Y η ^ q := by
        have := pow_nonneg (hY0 η) q
        nlinarith
      linarith
  have e5 : ∫ η, (m / 2 * Y η ^ (q + 1) - W / 2 * Y η ^ q) * ϱ η =
      m / 2 * (∫ η, Y η ^ (q + 1) * ϱ η) - W / 2 * ∫ η, Y η ^ q * ϱ η := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (iq1.const_mul _) (iq.const_mul _)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun η => by
      simp only []
      ring
  have e6 : ∫ η, ((2 * q + 3 * W) * Y η ^ q) * ϱ η = (2 * q + 3 * W) * ∫ η, Y η ^ q * ϱ η := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun η => by
      simp only []
      ring
  have hI0 : 0 ≤ ∫ η, Y η ^ q * ϱ η :=
    integral_nonneg fun η => mul_nonneg (pow_nonneg (hY0 η) _) (hϱ0 η)
  rw [e5] at hlow
  rw [e6] at hup
  nlinarith
end BallMoments
open BallMoments in
theorem gaussianMomentBound_proof : GaussianMomentBound := by
  intro ι _ _ ρ m κ W d Ψ K r hρ hm hκ hr hd hC hW hs q b₀
  set w : ι → ℝ := fun b => Real.exp (-(2 * κ * d b b₀)) with hw
  set Y := weightedSquare w with hY
  set ϱ := ballDensity r Ψ with hϱd
  have hϱ0 : ∀ η, 0 ≤ ϱ η := fun η => ballDensity_nonneg hr η
  have hW0 : 0 ≤ W := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hW b₀)
  have hmom : ∀ q : ℕ, ∫ η, Y η ^ q * ϱ η ≤
      (∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W)) / m ^ q * ∫ η, ϱ η := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      have hst := weightedSquare_moment_step hρ hm hκ hr hd hC hW hs b₀ q
      have hc : 0 ≤ 2 * (q : ℝ) + 4 * W := by positivity
      rw [Finset.prod_range_succ, pow_succ]
      have h1 : ∫ η, Y η ^ (q + 1) * ϱ η ≤ (2 / m) * ((2 * q + 4 * W) * ∫ η, Y η ^ q * ϱ η) := by
        have e : (2 / m) * (m / 2 * ∫ η, Y η ^ (q + 1) * ϱ η) = ∫ η, Y η ^ (q + 1) * ϱ η := by
          field_simp
        rw [← e]
        exact mul_le_mul_of_nonneg_left hst (by positivity)
      have h2 : (2 / m) * ((2 * q + 4 * W) * ∫ η, Y η ^ q * ϱ η) ≤
          (2 / m) * ((2 * q + 4 * W) *
            ((∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W)) / m ^ q * ∫ η, ϱ η)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left ih hc
      refine (h1.trans h2).trans (le_of_eq ?_)
      field_simp
      ring
  have hb₀ : ∀ η : BondField ι, ‖η b₀‖ ^ 2 ≤ Y η := by
    intro η
    have h1 : w b₀ * ‖η b₀‖ ^ 2 ≤ Y η := by
      apply Finset.single_le_sum (f := fun b => w b * ‖η b‖ ^ 2)
      · intro b _
        have : 0 < w b := Real.exp_pos _
        positivity
      · exact Finset.mem_univ b₀
    have h2 : w b₀ = 1 := by
      simp [hw, hd.self]
    rwa [h2, one_mul] at h1
  have hϱ : ContDiff ℝ 1 ϱ := contDiff_ballDensity hρ hr hC.smooth
  have hc : HasCompactSupport ϱ := hasCompactSupport_ballDensity hρ hr
  have hnorm : Continuous fun η : BondField ι => ‖η b₀‖ ^ (2 * q) :=
    ((continuous_apply b₀).norm).pow _
  have hY' : Continuous Y := (contDiff_weightedSquare w).continuous
  have hle : ∫ η, ‖η b₀‖ ^ (2 * q) * ϱ η ≤ ∫ η, Y η ^ q * ϱ η := by
    apply integral_mono (integrable_mul_of_hasCompactSupport hϱ.continuous hc hnorm)
      (integrable_mul_of_hasCompactSupport hϱ.continuous hc (hY'.pow q))
    intro η
    simp only []
    apply mul_le_mul_of_nonneg_right _ (hϱ0 η)
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (hb₀ η) q
  have hZ0 : 0 ≤ ∫ η, ϱ η := integral_nonneg hϱ0
  unfold ballExpectation
  have hC0 : 0 ≤ (∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W)) / m ^ q := by
    apply div_nonneg _ (by positivity)
    exact Finset.prod_nonneg fun k _ => by positivity
  rcases hZ0.lt_or_eq with hZ | hZ
  · rw [div_le_iff₀ hZ]
    exact hle.trans (hmom q)
  · rw [← hZ]
    simpa using hC0
end YangMills.Construction.ColdStepAtMirrorFrames
end
