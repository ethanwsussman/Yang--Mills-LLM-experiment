import YangMills.Construction.ClusterExpansionOfAStep.CovarianceOfAFunctionOfSomeBondsProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondMomentOfAConvexLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ConvexBallLaws
open YangMills.Construction.ColdStepAtMirrorFrames
namespace SecondMoment
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem hasDerivAt_fderiv_line {G : BondField ι → ℝ} (hG : Differentiable ℝ G) (ξ v : BondField ι) :
    HasDerivAt (fun t : ℝ => G (ξ + t • v)) (fderiv ℝ G ξ v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => ξ + t • v) v 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ξ
    simpa using this
  have hG0 : HasFDerivAt G (fderiv ℝ G ξ) (ξ + (0 : ℝ) • v) := by
    simpa using (hG ξ).hasFDerivAt
  exact hG0.comp_hasDerivAt (0 : ℝ) hline
theorem contDiff_radialCutoff_norm {R : ℝ} {χ : ℝ → ℝ} (hR : 0 < R) (hχ : IsRadialCutoff R χ) :
    ContDiff ℝ 1 fun x : BondVector => χ ‖x‖ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have : (fun x : BondVector => χ ‖x‖) =ᶠ[nhds 0] fun _ => (1 : ℝ) := by
      have hball : Metric.ball (0 : BondVector) (5 * R / 8) ∈ nhds (0 : BondVector) :=
        Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hball] with y hy
      have : ‖y‖ < 5 * R / 8 := by simpa using hy
      exact hχ.one _ (norm_nonneg _) this.le
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact hχ.smooth.contDiffAt.comp x (contDiffAt_norm ℝ hx)
theorem contDiff_radialWeightProd {R : ℝ} {χ : ℝ → ℝ} (hR : 0 < R) (hχ : IsRadialCutoff R χ) :
    ContDiff ℝ 1 (radialWeightProd (ι := ι) χ) := by
  unfold radialWeightProd
  apply contDiff_prod
  intro e _
  exact (contDiff_radialCutoff_norm hR hχ).comp (contDiff_apply ℝ BondVector e)
theorem radialCutoff_nonneg {R : ℝ} {χ : ℝ → ℝ} (hχ : IsRadialCutoff R χ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ χ t := by
  rcases lt_or_ge t R with h | h
  · exact (hχ.pos t ht h).le
  · rw [hχ.zero t h]
theorem radialWeightProd_nonneg {R : ℝ} {χ : ℝ → ℝ} (hχ : IsRadialCutoff R χ) (ξ : BondField ι) :
    0 ≤ radialWeightProd χ ξ :=
  Finset.prod_nonneg fun e _ => radialCutoff_nonneg hχ _ (norm_nonneg _)
theorem norm_lt_of_radialWeightProd_ne_zero {R : ℝ} {χ : ℝ → ℝ} (hχ : IsRadialCutoff R χ)
    (ξ : BondField ι) (h : radialWeightProd χ ξ ≠ 0) (e : ι) : ‖ξ e‖ < R := by
  by_contra hc
  push Not at hc
  exact h (Finset.prod_eq_zero (Finset.mem_univ e) (hχ.zero _ hc))
theorem fderiv_radialWeightProd_dilation_nonpos {R : ℝ} {χ : ℝ → ℝ} (hR : 0 < R)
    (hχ : IsRadialCutoff R χ) (ξ : BondField ι) (e : ι) :
    fderiv ℝ (radialWeightProd (ι := ι) χ) ξ (Pi.single e (ξ e) : BondField ι) ≤ 0 := by
  have hdiff : Differentiable ℝ (radialWeightProd (ι := ι) χ) :=
    (contDiff_radialWeightProd hR hχ).differentiable (by norm_num)
  have hline := hasDerivAt_fderiv_line hdiff ξ (Pi.single e (ξ e) : BondField ι)
  set c : ℝ := ∏ e' ∈ Finset.univ.erase e, χ ‖ξ e'‖ with hc
  have hc0 : 0 ≤ c := Finset.prod_nonneg fun e' _ => radialCutoff_nonneg hχ _ (norm_nonneg _)
  have hχd : HasDerivAt χ (deriv χ ‖ξ e‖) ‖ξ e‖ :=
    ((hχ.smooth.differentiable (by norm_num)) _).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => (1 + t) * ‖ξ e‖) ‖ξ e‖ 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ‖ξ e‖
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => c * χ ((1 + t) * ‖ξ e‖))
      (c * (deriv χ ‖ξ e‖ * ‖ξ e‖)) 0 := by
    have h3 : HasDerivAt χ (deriv χ ‖ξ e‖) ((1 + 0) * ‖ξ e‖) := by simpa using hχd
    exact (h3.comp (0 : ℝ) h1).const_mul c
  have heq : (fun t : ℝ => radialWeightProd χ (ξ + t • (Pi.single e (ξ e) : BondField ι))) =ᶠ[nhds 0]
      fun t : ℝ => c * χ ((1 + t) * ‖ξ e‖) := by
    have hnear : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hnear] with t ht
    unfold radialWeightProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e), mul_comm]
    congr 1
    · apply Finset.prod_congr rfl
      intro e' he'
      have hne : e' ≠ e := Finset.ne_of_mem_erase he'
      simp [Pi.single_eq_of_ne hne]
    · congr 1
      have hval : (ξ + t • (Pi.single e (ξ e) : BondField ι)) e = (1 + t) • ξ e := by
        simp [add_smul]
      rw [hval, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])]
  have hu := hline.unique (h2.congr_of_eventuallyEq heq)
  rw [hu]
  have hneg : deriv χ ‖ξ e‖ ≤ 0 := hχ.anti _ (norm_nonneg _)
  have := norm_nonneg (ξ e)
  exact mul_nonpos_of_nonneg_of_nonpos hc0 (mul_nonpos_of_nonpos_of_nonneg hneg this)
theorem contDiff_ballDensity {R : ℝ} {χ : ℝ → ℝ} {V : BondField ι → ℝ} (hR : 0 < R)
    (hχ : IsRadialCutoff R χ) (hV : ContDiff ℝ 3 V) : ContDiff ℝ 1 (ballDensity χ V) := by
  unfold ballDensity
  exact (contDiff_radialWeightProd hR hχ).mul ((hV.of_le (by norm_num)).neg.exp)
theorem hasCompactSupport_ballDensity {R : ℝ} {χ : ℝ → ℝ} {V : BondField ι → ℝ} (hR : 0 < R)
    (hχ : IsRadialCutoff R χ) : HasCompactSupport (ballDensity χ V) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) R) fun ξ hξ => ?_
  by_contra hne
  apply hξ
  have hW : radialWeightProd χ ξ ≠ 0 := fun h => hne (by simp [ballDensity, h])
  rw [mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg hR.le).mpr fun e => (norm_lt_of_radialWeightProd_ne_zero hχ ξ hW e).le
theorem ballDensity_nonneg {R : ℝ} {χ : ℝ → ℝ} {V : BondField ι → ℝ} (hχ : IsRadialCutoff R χ)
    (ξ : BondField ι) : 0 ≤ ballDensity χ V ξ :=
  mul_nonneg (radialWeightProd_nonneg hχ ξ) (Real.exp_pos _).le
theorem integrable_mul_of_hasCompactSupport {μ g : BondField ι → ℝ} (hμ : Continuous μ)
    (hc : HasCompactSupport μ) (hg : Continuous g) : Integrable (fun ξ => g ξ * μ ξ) := by
  apply Continuous.integrable_of_hasCompactSupport (hg.mul hμ)
  exact hc.mul_left
def bondDilation (e : ι) (ξ : BondField ι) : BondField ι := Pi.single e (ξ e)
theorem continuous_bondDilation (e : ι) : Continuous (bondDilation (ι := ι) e) := by
  unfold bondDilation
  exact (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) e).continuous.comp (continuous_apply e)
theorem integral_mul_fderiv_bondDilation {T μ : BondField ι → ℝ} (hT : ContDiff ℝ 1 T)
    (hμ : ContDiff ℝ 1 μ) (hc : HasCompactSupport μ) (e : ι) :
    ∫ ξ, T ξ * fderiv ℝ μ ξ (bondDilation e ξ) =
      - ∫ ξ, (fderiv ℝ T ξ (bondDilation e ξ) + 3 * T ξ) * μ ξ := by
  set P : Fin 3 → BondField ι →L[ℝ] ℝ := fun i =>
    (EuclideanSpace.proj i).comp (ContinuousLinearMap.proj e) with hP
  set f : Fin 3 → BondVector := fun i => EuclideanSpace.single i (1 : ℝ) with hf
  set v : Fin 3 → BondField ι := fun i => Pi.single e (f i) with hv
  have hT' : Differentiable ℝ T := hT.differentiable (by norm_num)
  have hμ' : Differentiable ℝ μ := hμ.differentiable (by norm_num)
  have hTc : Continuous T := hT.continuous
  have hFT : Continuous (fderiv ℝ T) := hT.continuous_fderiv (by norm_num)
  have hFμ : Continuous (fderiv ℝ μ) := hμ.continuous_fderiv (by norm_num)
  have hdil : ∀ ξ : BondField ι, bondDilation e ξ = ∑ i, P i ξ • v i := by
    intro ξ
    have e1 : ξ e = ∑ i, (ξ e) i • f i := by
      ext l
      simp [hf, Finset.sum_apply, Pi.single_apply]
    unfold bondDilation
    conv_lhs => rw [e1]
    simp only [hv, hP]
    have e2 : (Pi.single e (∑ i, (ξ e) i • f i) : BondField ι) =
        ∑ i, (ξ e) i • (Pi.single e (f i) : BondField ι) := by
      funext l
      by_cases h : l = e
      · subst h
        simp [Finset.sum_apply]
      · simp [Finset.sum_apply, Pi.single_eq_of_ne h]
    rw [e2]
    rfl
  have hPv : ∀ i, P i (v i) = 1 := by
    intro i
    simp [hP, hv, hf]
  have hcoord : ∀ (i : Fin 3) (ξ : BondField ι),
      fderiv ℝ (fun ζ => T ζ * P i ζ) ξ (v i) = fderiv ℝ T ξ (v i) * P i ξ + T ξ := by
    intro i ξ
    have h1 : fderiv ℝ (fun ζ => T ζ * P i ζ) ξ = _ :=
      ((hT' ξ).hasFDerivAt.mul (P i).hasFDerivAt).fderiv
    rw [h1]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hPv]
    ring
  have hvc : ∀ i, Continuous fun ξ => fderiv ℝ μ ξ (v i) := fun i => hFμ.clm_apply continuous_const
  have hFTv : ∀ i, Continuous fun ξ => fderiv ℝ T ξ (v i) := fun i => hFT.clm_apply continuous_const
  have key : ∀ i : Fin 3, ∫ ξ, (T ξ * P i ξ) * fderiv ℝ μ ξ (v i) =
      -∫ ξ, (fderiv ℝ T ξ (v i) * P i ξ + T ξ) * μ ξ := by
    intro i
    have hd : Differentiable ℝ (fun ζ => T ζ * P i ζ) := hT'.mul (P i).differentiable
    have c1 : Continuous fun ξ => (fderiv ℝ T ξ (v i) * P i ξ + T ξ) :=
      ((hFTv i).mul (P i).continuous).add hTc
    have i1 : Integrable fun ξ => fderiv ℝ (fun ζ => T ζ * P i ζ) ξ (v i) * μ ξ := by
      simp only [hcoord]
      exact integrable_mul_of_hasCompactSupport hμ.continuous hc c1
    have i2 : Integrable fun ξ => (T ξ * P i ξ) * fderiv ℝ μ ξ (v i) :=
      Continuous.integrable_of_hasCompactSupport ((hTc.mul (P i).continuous).mul (hvc i))
        (hc.fderiv_apply (𝕜 := ℝ) (v i)).mul_left
    have i3 : Integrable fun ξ => (T ξ * P i ξ) * μ ξ :=
      integrable_mul_of_hasCompactSupport hμ.continuous hc (hTc.mul (P i).continuous)
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3 (fun x _ => hd x)
      (fun x _ => hμ' x)
    simp only [hcoord] at this
    exact this
  have hL : ∀ ξ, T ξ * fderiv ℝ μ ξ (bondDilation e ξ) =
      ∑ i, (T ξ * P i ξ) * fderiv ℝ μ ξ (v i) := by
    intro ξ
    rw [hdil, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul]
    ring
  have hR : ∀ ξ, (fderiv ℝ T ξ (bondDilation e ξ) + 3 * T ξ) * μ ξ =
      ∑ i, (fderiv ℝ T ξ (v i) * P i ξ + T ξ) * μ ξ := by
    intro ξ
    rw [hdil, map_sum, ← Finset.sum_mul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_const]
    simp only [map_smul, smul_eq_mul, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [hL, hR]
  rw [integral_finset_sum, integral_finset_sum, ← Finset.sum_neg_distrib]
  · exact Finset.sum_congr rfl fun i _ => key i
  · intro i _
    exact integrable_mul_of_hasCompactSupport hμ.continuous hc (((hFTv i).mul (P i).continuous).add hTc)
  · intro i _
    exact Continuous.integrable_of_hasCompactSupport ((hTc.mul (P i).continuous).mul (hvc i))
      (hc.fderiv_apply (𝕜 := ℝ) (v i)).mul_left
theorem fderiv_ballDensity {R : ℝ} {χ : ℝ → ℝ} {V : BondField ι → ℝ} (hR : 0 < R)
    (hχ : IsRadialCutoff R χ) (hV : ContDiff ℝ 3 V) (ξ v : BondField ι) :
    fderiv ℝ (ballDensity χ V) ξ v = Real.exp (- V ξ) * fderiv ℝ (radialWeightProd χ) ξ v -
      ballDensity χ V ξ * fderiv ℝ V ξ v := by
  have hW := ((contDiff_radialWeightProd (ι := ι) hR hχ).differentiable (by norm_num) ξ).hasFDerivAt
  have hV' := ((hV.differentiable (by norm_num)) ξ).hasFDerivAt
  have hE := hV'.neg.exp
  have hform : ballDensity χ V = fun y => radialWeightProd χ y * Real.exp (- V y) := rfl
  have h : fderiv ℝ (fun y => radialWeightProd χ y * Real.exp (- V y)) ξ = _ := (hW.mul hE).fderiv
  rw [hform, h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.neg_apply, Pi.neg_apply]
  ring
theorem secondDerivAlong_eq_fderiv_fderiv {V : BondField ι → ℝ} (hV : ContDiff ℝ 3 V)
    (ζ u v : BondField ι) : secondDerivAlong V ζ u v = fderiv ℝ (fderiv ℝ V) ζ v u := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.secondDerivAlong_eq_fderiv_fderiv <;> assumption
theorem fderiv_fderiv_symm {V : BondField ι → ℝ} (hV : ContDiff ℝ 3 V) (ζ u v : BondField ι) :
    fderiv ℝ (fderiv ℝ V) ζ u v = fderiv ℝ (fderiv ℝ V) ζ v u :=
  (hV.contDiffAt.isSymmSndFDerivAt (by simp; norm_num)) u v
theorem weighted_hessian_lower_bound {R m κ : ℝ} {d : ι → ι → ℝ} {V : BondField ι → ℝ}
    {K : ι → ι → ℝ} (hR : 0 < R) (hκ : 0 ≤ κ) (hd : IsPseudoMetricOnBonds d)
    (hC : IsUniformlyConvexDecaying R m κ d V K) (b₀ : ι)
    (ζ ξ : BondField ι) (hζ : ∀ b, ‖ζ b‖ < R) :
    m * ∑ b, Real.exp (-(2 * κ * d b b₀)) * ‖ξ b‖ ^ 2 ≤
      ∑ b, Real.exp (-(2 * κ * d b b₀)) * secondDerivAlong V ζ (Pi.single b (ξ b)) ξ := by
  set H := fderiv ℝ (fderiv ℝ V) ζ with hH
  set U : ι → BondField ι := fun b => Pi.single b (ξ b) with hU
  set a : ι → ℝ := fun b => Real.exp (-(κ * d b b₀)) with ha
  set w : ι → ℝ := fun b => Real.exp (-(2 * κ * d b b₀)) with hw
  have hwa : ∀ b, w b = a b * a b := by
    intro b
    simp only [hw, ha]
    rw [← Real.exp_add]
    congr 1
    ring
  have ha0 : ∀ b, 0 < a b := fun b => Real.exp_pos _
  have hsumU : ∑ b, U b = ξ := Finset.univ_sum_single ξ
  have hdnn : ∀ b b', 0 ≤ d b b' := by
    intro b b'
    have h1 := hd.triangle b b' b
    rw [hd.self, hd.symm b' b] at h1
    linarith
  set A : ι → ι → ℝ := fun b b' => H (U b') (U b) with hA
  have hAs : ∀ b b', A b b' = A b' b := fun b b' => fderiv_fderiv_symm hC.smooth ζ _ _
  have hAb : ∀ b b', |A b b'| ≤ K b b' * ‖ξ b‖ * ‖ξ b'‖ := by
    intro b b'
    have h1 := hC.kernel ζ hζ b b' (ξ b) (ξ b')
    rw [secondDerivAlong_eq_fderiv_fderiv hC.smooth] at h1
    exact h1
  have hK0 : ∀ b b', 0 ≤ K b b' := by
    intro b b'
    obtain ⟨x, hx⟩ : ∃ x : BondVector, ‖x‖ = 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
    have h1 := hC.kernel 0 (fun _ => by simpa using hR) b b' x x
    rw [hx] at h1
    have := abs_nonneg (secondDerivAlong V 0 (bondVariation b x) (bondVariation b' x))
    nlinarith
  have hS1 : ∀ b, secondDerivAlong V ζ (U b) ξ = ∑ b', A b b' := by
    intro b
    rw [secondDerivAlong_eq_fderiv_fderiv hC.smooth]
    conv_lhs => rw [← hsumU]
    rw [map_sum, ContinuousLinearMap.sum_apply]
  set χ : BondField ι := fun b => a b • ξ b with hχ
  have hχU : χ = ∑ b, a b • U b := by
    funext l
    simp only [hχ, hU, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    simp
  have hfl := hC.floor ζ hζ χ
  have hS2 : secondDerivAlong V ζ χ χ = ∑ b, ∑ b', a b * a b' * A b b' := by
    rw [secondDerivAlong_eq_fderiv_fderiv hC.smooth, hχU]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro b' _
    simp only [hA]
    ring
  set x : ι → ℝ := fun b => a b * ‖ξ b‖ with hx
  have hxY : ∀ b, w b * ‖ξ b‖ ^ 2 = x b ^ 2 := by
    intro b
    simp only [hx, hwa]
    ring
  have hχn : ∀ b, ‖χ b‖ ^ 2 = x b ^ 2 := by
    intro b
    simp only [hχ, hx]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ha0 b)]
  set c : ι → ι → ℝ := fun b b' => K b b' * (Real.exp (2 * κ * d b b') - 1) with hc
  have hc0 : ∀ b b', 0 ≤ c b b' := by
    intro b b'
    have : 1 ≤ Real.exp (2 * κ * d b b') := Real.one_le_exp (by
      have := hdnn b b'
      positivity)
    exact mul_nonneg (hK0 b b') (by linarith)
  have hcs : ∀ b b', c b b' = c b' b := by
    intro b b'
    simp only [hc]
    rw [hC.symm b b', hd.symm b b']
  have hratio : ∀ b b', a b ≤ a b' * Real.exp (2 * κ * d b b') := by
    intro b b'
    simp only [ha]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := hd.triangle b' b b₀
    have h2 := hdnn b b'
    rw [hd.symm b' b] at h1
    nlinarith
  have hterm : ∀ b b', |(a b - a b') ^ 2 * A b b'| ≤ c b b' * (x b ^ 2 + x b' ^ 2) := by
    intro b b'
    set E := Real.exp (2 * κ * d b b') with hE
    have h1 := hratio b b'
    have h2 : a b' ≤ a b * E := by
      have := hratio b' b
      rwa [hd.symm b' b] at this
    have hE1 : 1 ≤ E := Real.one_le_exp (by
      have := hdnn b b'
      positivity)
    have hab := ha0 b
    have hab' := ha0 b'
    have h3 : (a b - a b') ^ 2 ≤ 2 * (a b * a b') * (E - 1) := by nlinarith
    have h4 : |A b b'| ≤ K b b' * ‖ξ b‖ * ‖ξ b'‖ := hAb b b'
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc (a b - a b') ^ 2 * |A b b'|
        ≤ (2 * (a b * a b') * (E - 1)) * (K b b' * ‖ξ b‖ * ‖ξ b'‖) :=
          mul_le_mul h3 h4 (abs_nonneg _) (by
            have := hK0 b b'
            have : 0 ≤ E - 1 := by linarith
            positivity)
      _ = c b b' * (2 * (x b * x b')) := by
          simp only [hc, hx]
          ring
      _ ≤ c b b' * (x b ^ 2 + x b' ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (hc0 b b')
          nlinarith [sq_nonneg (x b - x b')]
  set S1 := ∑ b, ∑ b', w b * A b b' with hS1d
  set S2 := ∑ b, ∑ b', a b * a b' * A b b' with hS2d
  have hswap : S1 = ∑ b, ∑ b', w b' * A b b' := by
    simp only [hS1d]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro b' _
    rw [hAs]
  have hdiff : 2 * S1 - 2 * S2 = ∑ b, ∑ b', (a b - a b') ^ 2 * A b b' := by
    have e1 : 2 * S1 = S1 + ∑ b, ∑ b', w b' * A b b' := by
      rw [← hswap]
      ring
    rw [e1]
    simp only [hS1d, hS2d, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro b' _
    rw [hwa b, hwa b']
    ring
  have hbound : |∑ b, ∑ b', (a b - a b') ^ 2 * A b b'| ≤ 2 * m * ∑ b, x b ^ 2 := by
    have h1 : |∑ b, ∑ b', (a b - a b') ^ 2 * A b b'| ≤
        ∑ b, ∑ b', c b b' * (x b ^ 2 + x b' ^ 2) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => hterm b b')
    have h2 : ∑ b, ∑ b', c b b' * (x b ^ 2 + x b' ^ 2) = 2 * ∑ b, (∑ b', c b b') * x b ^ 2 := by
      have e2 : ∑ b, ∑ b', c b b' * x b' ^ 2 = ∑ b, ∑ b', c b b' * x b ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro b' _
        rw [hcs]
      simp only [mul_add, Finset.sum_add_distrib]
      rw [e2]
      simp only [Finset.sum_mul]
      ring
    have h3 : ∑ b, (∑ b', c b b') * x b ^ 2 ≤ m * ∑ b, x b ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_right (hC.standingConstraints b) (sq_nonneg _)
    rw [h2] at h1
    linarith
  have hfloor2 : 2 * m * ∑ b, x b ^ 2 ≤ S2 := by
    have h1 := hfl
    rw [hS2] at h1
    simp only [hχn] at h1
    exact h1
  have hT1 : ∑ b, w b * secondDerivAlong V ζ (Pi.single b (ξ b)) ξ = S1 := by
    simp only [hS1d, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.mul_sum]
    congr 1
    exact hS1 b
  have hY : ∑ b, w b * ‖ξ b‖ ^ 2 = ∑ b, x b ^ 2 := Finset.sum_congr rfl fun b _ => hxY b
  rw [hT1, hY]
  have := abs_le.mp hbound
  linarith [this.1]
theorem weighted_slope_lower_bound {R m κ : ℝ} {d : ι → ι → ℝ} {V : BondField ι → ℝ}
    {K : ι → ι → ℝ} (hR : 0 < R) (hm : 0 < m) (hκ : 0 ≤ κ) (hd : IsPseudoMetricOnBonds d)
    (hC : IsUniformlyConvexDecaying R m κ d V K) (b₀ : ι) (ξ : BondField ι) (hξ : ∀ b, ‖ξ b‖ < R) :
    m / 2 * (∑ b, Real.exp (-(2 * κ * d b b₀)) * ‖ξ b‖ ^ 2) -
        (2 * m)⁻¹ * ∑ b, Real.exp (-(2 * κ * d b b₀)) * bondGradNorm V b 0 ^ 2 ≤
      ∑ b, Real.exp (-(2 * κ * d b b₀)) * fderiv ℝ V ξ (bondDilation b ξ) := by
  set w : ι → ℝ := fun b => Real.exp (-(2 * κ * d b b₀)) with hw
  set S : ι → ℝ := fun b => bondGradNorm V b 0 with hS
  have hw0 : ∀ b, 0 < w b := fun b => Real.exp_pos _
  have hdiff2 : ∀ u : BondField ι, Differentiable ℝ fun ζ => fderiv ℝ V ζ u := by
    intro u
    have h2 : Differentiable ℝ (fderiv ℝ V) :=
      (hC.smooth.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
    exact fun ζ => ((h2 ζ).hasFDerivAt.clm_apply (hasFDerivAt_const u ζ)).differentiableAt
  set g : ℝ → ℝ := fun t => ∑ b, w b * fderiv ℝ V (t • ξ) (bondDilation b ξ) with hg
  set g' : ℝ → ℝ := fun t => ∑ b, w b * secondDerivAlong V (t • ξ) (bondDilation b ξ) ξ with hg'
  have hder : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    apply HasDerivAt.fun_sum
    intro b _
    apply HasDerivAt.const_mul
    have h1 : HasDerivAt (fun t : ℝ => t • ξ) ξ t := by
      simpa using (hasDerivAt_id t).smul_const ξ
    exact ((hdiff2 (bondDilation b ξ) (t • ξ)).hasFDerivAt).comp_hasDerivAt t h1
  obtain ⟨θ, hθ, hmv⟩ := exists_hasDerivAt_eq_slope g g' (zero_lt_one)
    (continuous_iff_continuousAt.mpr fun t => (hder t).continuousAt).continuousOn
    (fun t _ => hder t)
  have hθξ : ∀ b, ‖(θ • ξ) b‖ < R := by
    intro b
    have : (θ • ξ) b = θ • ξ b := rfl
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hθ.1]
    have h1 := hξ b
    have h2 := norm_nonneg (ξ b)
    nlinarith [hθ.2]
  have hfl := weighted_hessian_lower_bound hR hκ hd hC b₀ (θ • ξ) ξ hθξ
  have e1 : g 1 = ∑ b, w b * fderiv ℝ V ξ (bondDilation b ξ) := by
    simp only [hg, one_smul]
  have e0 : g 0 = ∑ b, w b * fderiv ℝ V 0 (bondDilation b ξ) := by
    simp only [hg, zero_smul]
  have hpart : ∀ b, |fderiv ℝ V 0 (bondDilation b ξ)| ≤ S b * ‖ξ b‖ := by
    intro b
    have := ((fderiv ℝ V 0).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)).le_opNorm
      (ξ b)
    simpa [bondDilation, hS, bondGradNorm] using this
  have hg0 : -(∑ b, w b * (S b * ‖ξ b‖)) ≤ g 0 := by
    rw [e0, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro b _
    have h1 := hpart b
    have h2 := neg_abs_le (fderiv ℝ V 0 (bondDilation b ξ))
    have h3 := hw0 b
    nlinarith
  have hsq : ∑ b, w b * (S b * ‖ξ b‖) ≤
      m / 2 * (∑ b, w b * ‖ξ b‖ ^ 2) + (2 * m)⁻¹ * ∑ b, w b * S b ^ 2 := by
    have h1 : ∀ b, w b * (S b * ‖ξ b‖) ≤
        m / 2 * (w b * ‖ξ b‖ ^ 2) + (2 * m)⁻¹ * (w b * S b ^ 2) := by
      intro b
      have h3 : 0 ≤ (2 * m)⁻¹ * (m * ‖ξ b‖ - S b) ^ 2 := by positivity
      have e : (2 * m)⁻¹ * (m * ‖ξ b‖ - S b) ^ 2 =
          m / 2 * ‖ξ b‖ ^ 2 - S b * ‖ξ b‖ + (2 * m)⁻¹ * S b ^ 2 := by
        field_simp
        ring
      rw [e] at h3
      have h4 := mul_nonneg (hw0 b).le h3
      nlinarith [h4]
    calc ∑ b, w b * (S b * ‖ξ b‖)
        ≤ ∑ b, (m / 2 * (w b * ‖ξ b‖ ^ 2) + (2 * m)⁻¹ * (w b * S b ^ 2)) :=
          Finset.sum_le_sum fun b _ => h1 b
      _ = m / 2 * (∑ b, w b * ‖ξ b‖ ^ 2) + (2 * m)⁻¹ * ∑ b, w b * S b ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have e3 : m * (∑ b, w b * ‖ξ b‖ ^ 2) ≤ g' θ := hfl
  rw [← e1]
  linarith
end SecondMoment
open SecondMoment in
theorem secondMomentBound_holds (hcut : CutoffFactorIsRadialCutoff) : SecondMomentBound := by
  intro ι _ _ R m κ W d V K p hR hm hκ hp hd hC hW b₀
  set χ : ℝ → ℝ := fun t => cutoffFactor R p (max t 0) with hχdef
  have hχ : IsRadialCutoff R χ := hcut R p hR hp
  have e_dens : ballDensity (cutoffFactor R p) V = ballDensity χ V := by
    funext ξ
    unfold ballDensity radialWeightProd
    congr 1
    exact Finset.prod_congr rfl fun b _ => by simp [hχdef, max_eq_left (norm_nonneg (ξ b))]
  unfold ballExpectation
  rw [e_dens]
  set w : ι → ℝ := fun b => Real.exp (-(2 * κ * d b b₀)) with hw
  set μ := ballDensity χ V with hμd
  set Q : ℝ := ∑ b, w b * bondGradNorm V b 0 ^ 2 with hQ
  have hw0 : ∀ b, 0 < w b := fun b => Real.exp_pos _
  have hμ : ContDiff ℝ 1 μ := contDiff_ballDensity hR hχ hC.smooth
  have hc : HasCompactSupport μ := hasCompactSupport_ballDensity hR hχ
  have hμc : Continuous μ := hμ.continuous
  have hμ0 : ∀ ξ, 0 ≤ μ ξ := fun ξ => ballDensity_nonneg hχ ξ
  have hZ0 : 0 ≤ ∫ ξ, μ ξ := integral_nonneg hμ0
  have hW0 : 0 ≤ W := (Finset.sum_nonneg fun b _ => (hw0 b).le).trans (hW b₀)
  have hB0 : 0 ≤ 6 * W / m + (m ^ 2)⁻¹ * Q := by positivity
  rcases hZ0.lt_or_eq with hZ | hZ
  swap
  · rw [← hZ]
    simpa using hB0
  rw [div_le_iff₀ hZ]
  set Z : ℝ := ∫ ξ, μ ξ with hZd
  have hdc : ∀ (G : BondField ι → ℝ), ContDiff ℝ 1 G → ∀ b,
      Continuous fun ξ => fderiv ℝ G ξ (bondDilation b ξ) := fun G hG b =>
    (hG.continuous_fderiv (by norm_num)).clm_apply (continuous_bondDilation b)
  have hV1 : ContDiff ℝ 1 V := hC.smooth.of_le (by norm_num)
  have hb : ∀ b, ∫ ξ, fderiv ℝ V ξ (bondDilation b ξ) * μ ξ ≤ 3 * Z := by
    intro b
    have hbp := integral_mul_fderiv_bondDilation (T := fun _ => (1 : ℝ)) contDiff_const hμ hc b
    have i1 : Integrable fun ξ => fderiv ℝ μ ξ (bondDilation b ξ) := by
      refine Continuous.integrable_of_hasCompactSupport (hdc μ hμ b) ?_
      refine (hc.fderiv (𝕜 := ℝ)).mono ?_
      intro ξ hξ
      simp only [Function.mem_support] at hξ ⊢
      intro h0
      apply hξ
      simp [h0]
    have i2 : Integrable fun ξ => -(fderiv ℝ V ξ (bondDilation b ξ) * μ ξ) :=
      (integrable_mul_of_hasCompactSupport hμc hc (hdc V hV1 b)).neg
    have hle : ∫ ξ, fderiv ℝ μ ξ (bondDilation b ξ) ≤
        ∫ ξ, -(fderiv ℝ V ξ (bondDilation b ξ) * μ ξ) := by
      apply integral_mono i1 i2
      intro ξ
      have hs1 := fderiv_ballDensity hR hχ hC.smooth ξ (bondDilation b ξ)
      have hs2 := fderiv_radialWeightProd_dilation_nonpos (ι := ι) hR hχ ξ b
      have hE := Real.exp_pos (- V ξ)
      simp only []
      rw [hs1]
      have h1 : Real.exp (- V ξ) * fderiv ℝ (radialWeightProd χ) ξ (bondDilation b ξ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hE.le hs2
      have : ballDensity χ V ξ = μ ξ := rfl
      rw [this]
      linarith
    rw [integral_neg] at hle
    have e : ∫ ξ, fderiv ℝ μ ξ (bondDilation b ξ) = - (3 * Z) := by
      have e1 : ∀ ξ, (fderiv ℝ (fun _ : BondField ι => (1 : ℝ)) ξ (bondDilation b ξ) + 3 * 1) * μ ξ =
          3 * μ ξ := by
        intro ξ
        simp
      simp only [one_mul, e1] at hbp
      rw [hbp, integral_const_mul]
    rw [e] at hle
    linarith
  have hsum : ∫ ξ, (∑ b, w b * fderiv ℝ V ξ (bondDilation b ξ)) * μ ξ ≤ 3 * W * Z := by
    have e : ∫ ξ, (∑ b, w b * fderiv ℝ V ξ (bondDilation b ξ)) * μ ξ =
        ∑ b, w b * ∫ ξ, fderiv ℝ V ξ (bondDilation b ξ) * μ ξ := by
      simp only [Finset.sum_mul, mul_assoc]
      rw [integral_finset_sum]
      · exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
      · intro b _
        exact (integrable_mul_of_hasCompactSupport hμc hc (hdc V hV1 b)).const_mul _
    rw [e]
    calc ∑ b, w b * ∫ ξ, fderiv ℝ V ξ (bondDilation b ξ) * μ ξ ≤ ∑ b, w b * (3 * Z) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hb b) (hw0 b).le
      _ = (∑ b, w b) * (3 * Z) := by rw [Finset.sum_mul]
      _ ≤ W * (3 * Z) := mul_le_mul_of_nonneg_right (hW b₀) (by positivity)
      _ = 3 * W * Z := by ring
  set Y : BondField ι → ℝ := fun ξ => ∑ b, w b * ‖ξ b‖ ^ 2 with hY
  have hYc : Continuous Y := by
    apply continuous_finset_sum
    intro b _
    exact continuous_const.mul (((continuous_apply b).norm).pow 2)
  have hpt : ∫ ξ, (m / 2 * Y ξ - (2 * m)⁻¹ * Q) * μ ξ ≤
      ∫ ξ, (∑ b, w b * fderiv ℝ V ξ (bondDilation b ξ)) * μ ξ := by
    apply integral_mono
    · exact integrable_mul_of_hasCompactSupport hμc hc ((continuous_const.mul hYc).sub continuous_const)
    · apply integrable_mul_of_hasCompactSupport hμc hc
      exact continuous_finset_sum _ fun b _ => continuous_const.mul (hdc V hV1 b)
    · intro ξ
      simp only []
      by_cases h0 : μ ξ = 0
      · simp [h0]
      · have hP : radialWeightProd χ ξ ≠ 0 := fun h => h0 (by simp [hμd, ballDensity, h])
        exact mul_le_mul_of_nonneg_right
          (weighted_slope_lower_bound hR hm hκ hd hC b₀ ξ fun b =>
            norm_lt_of_radialWeightProd_ne_zero hχ ξ hP b) (hμ0 ξ)
  have e1 : ∫ ξ, (m / 2 * Y ξ - (2 * m)⁻¹ * Q) * μ ξ =
      m / 2 * (∫ ξ, Y ξ * μ ξ) - (2 * m)⁻¹ * Q * Z := by
    have : ∀ ξ, (m / 2 * Y ξ - (2 * m)⁻¹ * Q) * μ ξ =
        m / 2 * (Y ξ * μ ξ) - (2 * m)⁻¹ * Q * μ ξ := fun ξ => by ring
    simp only [this]
    rw [integral_sub ((integrable_mul_of_hasCompactSupport hμc hc hYc).const_mul _)
      (hμc.integrable_of_hasCompactSupport hc |>.const_mul _), integral_const_mul,
      integral_const_mul]
  have hYle : ∫ ξ, ‖ξ b₀‖ ^ 2 * μ ξ ≤ ∫ ξ, Y ξ * μ ξ := by
    apply integral_mono (integrable_mul_of_hasCompactSupport hμc hc (((continuous_apply b₀).norm).pow 2))
      (integrable_mul_of_hasCompactSupport hμc hc hYc)
    intro ξ
    simp only []
    apply mul_le_mul_of_nonneg_right _ (hμ0 ξ)
    have h1 : w b₀ * ‖ξ b₀‖ ^ 2 ≤ Y ξ := by
      apply Finset.single_le_sum (f := fun b => w b * ‖ξ b‖ ^ 2)
      · intro b _
        have : 0 < w b := hw0 b
        positivity
      · exact Finset.mem_univ b₀
    have h2 : w b₀ = 1 := by
      simp [hw, hd.self]
    rwa [h2, one_mul] at h1
  have hfin : m / 2 * (∫ ξ, Y ξ * μ ξ) ≤ (3 * W + (2 * m)⁻¹ * Q) * Z := by
    have := hpt.trans hsum
    rw [e1] at this
    linarith
  have : ∫ ξ, Y ξ * μ ξ ≤ (6 * W / m + (m ^ 2)⁻¹ * Q) * Z := by
    have e : (6 * W / m + (m ^ 2)⁻¹ * Q) * Z = 2 / m * ((3 * W + (2 * m)⁻¹ * Q) * Z) := by
      field_simp
      ring
    rw [e]
    have e' : ∫ ξ, Y ξ * μ ξ = 2 / m * (m / 2 * ∫ ξ, Y ξ * μ ξ) := by
      field_simp
    rw [e']
    exact mul_le_mul_of_nonneg_left hfin (by positivity)
  exact hYle.trans this
end YangMills.Construction.ConvexBallLaws
end
