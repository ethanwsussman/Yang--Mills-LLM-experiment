import YangMills.Construction.ClusterExpansionOfAStep.BondsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.CutOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.HessianFloorOfTheCostForm
import YangMills.Construction.ClusterExpansionOfAStep.MeanOfTheGain
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfTheLogOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.SlopeAtTheFrames
import YangMills.Construction.ClusterExpansionOfAStep.SlopeOfTheLogOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheWeightsOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfTheLawOfASetting
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings TorusBalls
  StepFloors
namespace GainMean
section LineDerivatives
variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev TangentField (ι : Type) : Type := ι → EuclideanSpace ℝ (Fin 3)
theorem update_add_smul_eq (η : TangentField ι) (b : ι) (X : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    Function.update η b (η b + τ • X) = η + τ • (Pi.single b X : TangentField ι) := by
  funext c
  by_cases h : c = b
  · subst h
    simp
  · simp [h]
theorem deriv_line_eq_fderiv {u : TangentField ι → ℝ} {η e : TangentField ι} (h : DifferentiableAt ℝ u η) :
    deriv (fun τ : ℝ => u (η + τ • e)) 0 = fderiv ℝ u η e := by
  have h1 : HasDerivAt (fun τ : ℝ => η + τ • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add η
  have h2 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h.hasFDerivAt h1 (by simp)
  exact h2.deriv
theorem deriv_deriv_line_eq {u : TangentField ι → ℝ} {U : Set (TangentField ι)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {η : TangentField ι} (hη : η ∈ U) (e e' : TangentField ι) :
    deriv (fun τ : ℝ => deriv (fun τ' : ℝ => u (η + τ • e + τ' • e')) 0) 0 =
      fderiv ℝ (fderiv ℝ u) η e e' := by
  have hat : ContDiffAt ℝ 2 u η := hu.contDiffAt (hU.mem_nhds hη)
  have hline : Filter.Tendsto (fun τ : ℝ => η + τ • e) (𝓝 0) (𝓝 η) := by
    have : Continuous fun τ : ℝ => η + τ • e := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ ξ in 𝓝 η, DifferentiableAt ℝ u ξ :=
    (hat.eventually (by simp)).mono fun ξ h => h.differentiableAt (by norm_num)
  have hev' : ∀ᶠ τ : ℝ in 𝓝 0, deriv (fun τ' : ℝ => u (η + τ • e + τ' • e')) 0 =
      fderiv ℝ u (η + τ • e) e' :=
    (hline.eventually hev).mono fun τ h => deriv_line_eq_fderiv h
  rw [Filter.EventuallyEq.deriv_eq hev']
  have hD : DifferentiableAt ℝ (fderiv ℝ u) η :=
    (hat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun τ : ℝ => η + τ • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add η
  have h2 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hD.hasFDerivAt h1 (by simp)
  have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) e')
  simpa using h3.deriv
theorem deriv_deriv_update_eq {u : TangentField ι → ℝ} {U : Set (TangentField ι)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {η : TangentField ι} (hη : η ∈ U) (b b' : ι) (X X' : EuclideanSpace ℝ (Fin 3)) :
    deriv (fun τ : ℝ => deriv (fun τ' : ℝ =>
      u (Function.update (Function.update η b (η b + τ • X)) b'
        ((Function.update η b (η b + τ • X)) b' + τ' • X'))) 0) 0 =
      fderiv ℝ (fderiv ℝ u) η (Pi.single b X : TangentField ι) (Pi.single b' X' : TangentField ι) := by
  simp only [update_add_smul_eq]
  exact deriv_deriv_line_eq hU hu hη _ _
theorem abs_apply_single_le {D : TangentField ι →L[ℝ] TangentField ι →L[ℝ] ℝ} {m : ℝ} {b b' : ι}
    (hD : ∀ X X' : EuclideanSpace ℝ (Fin 3), ‖X‖ = 1 → ‖X'‖ = 1 →
      |D (Pi.single b X : TangentField ι) (Pi.single b' X' : TangentField ι)| ≤ m)
    (X Z : EuclideanSpace ℝ (Fin 3)) :
    |D (Pi.single b X : TangentField ι) (Pi.single b' Z : TangentField ι)| ≤ m * ‖Z‖ * ‖X‖ := by
  by_cases hX : X = 0
  · simp [hX]
  by_cases hZ : Z = 0
  · simp [hZ]
  have hXn : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  have hZn : ‖Z‖ ≠ 0 := norm_ne_zero_iff.mpr hZ
  have h1 := hD (‖X‖⁻¹ • X) (‖Z‖⁻¹ • Z) (norm_smul_inv_norm hX) (norm_smul_inv_norm hZ)
  have e1 : (Pi.single b X : TangentField ι) = ‖X‖ • (Pi.single b (‖X‖⁻¹ • X) : TangentField ι) := by
    rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hXn, one_smul]
  have e2 : (Pi.single b' Z : TangentField ι) = ‖Z‖ • (Pi.single b' (‖Z‖⁻¹ • Z) : TangentField ι) := by
    rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hZn, one_smul]
  rw [e1, e2, map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul, abs_mul, abs_mul,
    abs_of_nonneg (norm_nonneg X), abs_of_nonneg (norm_nonneg Z)]
  have h2 : 0 ≤ ‖X‖ * ‖Z‖ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]
theorem abs_fderiv_sub_le {u : TangentField ι → ℝ} {U : Set (TangentField ι)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U)
    {K : Set (TangentField ι)} (hK : Convex ℝ K) (hKU : K ⊆ U) (h0 : (0 : TangentField ι) ∈ K) {M : ι → ι → ℝ}
    (hM : ∀ ξ ∈ K, ∀ (b b' : ι) (X X' : EuclideanSpace ℝ (Fin 3)), ‖X‖ = 1 → ‖X'‖ = 1 →
      |fderiv ℝ (fderiv ℝ u) ξ (Pi.single b X : TangentField ι) (Pi.single b' X' : TangentField ι)| ≤ M b b')
    {ζ : TangentField ι} (hζ : ζ ∈ K) (b : ι) (X : EuclideanSpace ℝ (Fin 3)) :
    |fderiv ℝ u ζ (Pi.single b X : TangentField ι) - fderiv ℝ u 0 (Pi.single b X : TangentField ι)| ≤
      (∑ b', M b b' * ‖ζ b'‖) * ‖X‖ := by
  set e : TangentField ι := Pi.single b X with he
  have hseg : ∀ θ ∈ Set.Icc (0 : ℝ) 1, θ • ζ ∈ K := by
    intro θ hθ
    have := hK h0 hζ (sub_nonneg.mpr hθ.2) hθ.1 (by ring)
    simpa using this
  have hderiv : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun θ : ℝ => fderiv ℝ u (θ • ζ) e)
      (fderiv ℝ (fderiv ℝ u) (θ • ζ) ζ e) (Set.Icc 0 1) θ := by
    intro θ hθ
    have hat : ContDiffAt ℝ 2 u (θ • ζ) := hu.contDiffAt (hU.mem_nhds (hKU (hseg θ hθ)))
    have hD : DifferentiableAt ℝ (fderiv ℝ u) (θ • ζ) :=
      (hat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h1 : HasDerivAt (fun θ : ℝ => θ • ζ) ζ θ := by
      simpa using (hasDerivAt_id θ).smul_const ζ
    have h2 := HasFDerivAt.comp_hasDerivAt θ hD.hasFDerivAt h1
    have h3 := h2.clm_apply (hasDerivAt_const θ e)
    simpa using h3.hasDerivWithinAt
  have hbound : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ u) (θ • ζ) ζ e‖ ≤
      (∑ b', M b b' * ‖ζ b'‖) * ‖X‖ := by
    intro θ hθ
    set ξ := θ • ζ with hξ
    have hat : ContDiffAt ℝ 2 u ξ := hu.contDiffAt (hU.mem_nhds (hKU (hseg θ hθ)))
    have hsymm : IsSymmSndFDerivAt ℝ u ξ := hat.isSymmSndFDerivAt (by simp)
    have hsum : ζ = ∑ b', (Pi.single b' (ζ b') : TangentField ι) := (Finset.univ_sum_single ζ).symm
    have h1 : fderiv ℝ (fderiv ℝ u) ξ ζ e =
        ∑ b', fderiv ℝ (fderiv ℝ u) ξ e (Pi.single b' (ζ b') : TangentField ι) := by
      rw [hsymm.eq ζ e]
      conv_lhs => rw [hsum]
      rw [map_sum]
    rw [h1, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun b' _ => ?_
    exact abs_apply_single_le (fun X X' hX hX' => hM ξ (hseg θ hθ) b b' X X' hX hX') X (ζ b')
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
  simpa using this
theorem sum_integral_partial_eq_sub {f : TangentField ι → ℝ} {U : Set (TangentField ι)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {η : TangentField ι} (hseg : ∀ v ∈ Set.Icc (0 : ℝ) 1, v • η ∈ U) :
    ∑ b, ∫ v in (0 : ℝ)..1, deriv (fun τ : ℝ => f (v • η + τ • (Pi.single b (η b) : TangentField ι))) 0 =
      f η - f 0 := by
  have hcont : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ v ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f (v • η) := fun v hv =>
    (hf.contDiffAt (hU.mem_nhds (hseg v hv))).differentiableAt (by norm_num)
  have hline : ContinuousOn (fun v : ℝ => v • η) (Set.Icc 0 1) := by fun_prop
  have hcv : ContinuousOn (fun v : ℝ => fderiv ℝ f (v • η)) (Set.Icc 0 1) :=
    hcont.comp hline hseg
  have hI : ∀ e : TangentField ι, IntervalIntegrable (fun v : ℝ => fderiv ℝ f (v • η) e) volume 0 1 := by
    intro e
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact hcv.clm_apply continuousOn_const
  have h1 : ∀ b, ∫ v in (0 : ℝ)..1, deriv (fun τ : ℝ => f (v • η + τ • (Pi.single b (η b) : TangentField ι))) 0 =
      ∫ v in (0 : ℝ)..1, fderiv ℝ f (v • η) (Pi.single b (η b) : TangentField ι) := by
    intro b
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le zero_le_one] at hv
    exact deriv_line_eq_fderiv (hdiff v hv)
  simp only [h1]
  rw [← intervalIntegral.integral_finset_sum fun b _ => hI _]
  have h2 : ∀ v : ℝ, ∑ b, fderiv ℝ f (v • η) (Pi.single b (η b) : TangentField ι) = fderiv ℝ f (v • η) η := by
    intro v
    rw [← map_sum, Finset.univ_sum_single]
  simp only [h2]
  have hder : ∀ v ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => f (v • η)) (fderiv ℝ f (v • η) η) v := by
    intro v hv
    rw [Set.uIcc_of_le zero_le_one] at hv
    have h3 : HasDerivAt (fun v : ℝ => v • η) η v := by
      simpa using (hasDerivAt_id v).smul_const η
    exact (hdiff v hv).hasFDerivAt.comp_hasDerivAt v h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hI η)]
  simp
end LineDerivatives
section ChartSettings
variable {R : StepSetup} {n : ℕ} [NeZero n] (s : ChartSetting R n)
theorem singleBond_eq (b : s.free) (η : FreeCoords s.free) :
    singleBond b η = (Pi.single b (η b) : TangentField s.free) := by
  funext b'
  by_cases h : b' = b
  · subst h
    simp [singleBond]
  · simp [singleBond, h]
theorem contDiff_restrictTo (X : Finset s.free) : ContDiff ℝ 3 (s.restrictTo X) := by
  refine contDiff_pi.mpr fun b => ?_
  unfold ChartSetting.restrictTo
  by_cases h : b ∈ X
  · simp only [h, if_true]
    exact contDiff_apply ℝ _ b
  · simp only [h, if_false]
    exact contDiff_const
theorem sum_freeBondsAt {M : Type} [AddCommMonoid M] (g : s.free → M) :
    ∑ Y : TorusSite n, ∑ b ∈ freeBondsAt s.free Y, g b = ∑ b, g b := by
  classical
  unfold freeBondsAt
  exact Finset.sum_fiberwise _ _ _
theorem restrictedSplit_totalCost (lam : ℝ) (X : Finset s.free) (ξ : FreeCoords s.free) :
    (s.restrictedSplit lam X).totalCost ξ =
      s.totalCost (s.restrictTo X ξ) + lam / 2 * ∑ b ∈ Finset.univ \ X, ‖ξ b‖ ^ 2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.Restriction.restrictedSplit_totalCost_eq <;> assumption
theorem partPotential_zero_eq (ξ : FreeCoords s.free) :
    s.partPotential 0 ξ = R.coupling * s.totalCost ξ - ∑ Y : TorusSite n, s.logJacobianAt Y ξ := by
  unfold ChartSetting.partPotential ChartSetting.totalCost ChartSetting.blockCostAt ChartSetting.logJacobianAt
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun Y _ => ?_
  ring
theorem restrictTo_zero (X : Finset s.free) : s.restrictTo X 0 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.Restriction.restrictTo_zero <;> assumption
theorem restrictedSplit_totalInteraction (lam : ℝ) (X : Finset s.free) {U : Set (FreeCoords s.free)}
    (hU : IsOpen U) (hU' : ∀ η, s.InBalls η → η ∈ U) (hc : ContDiffOn ℝ 3 s.totalCost U)
    (hρ : 0 ≤ R.ballRadius) {η : FreeCoords s.free}
    (hη : s.InBalls η) (hcut : ∀ ξ, s.InBalls ξ → s.InBalls (s.restrictTo X ξ))
    (hseg : ∀ v ∈ Set.Icc (0 : ℝ) 1, s.InBalls (v • η)) :
    (s.restrictedSplit lam X).totalInteraction η = s.partPotential 0 (s.restrictTo X η) +
      R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2 - s.partPotential 0 0 := by
  classical
  set D := s.restrictedSplit lam X with hD
  set U' : Set (FreeCoords s.free) := s.restrictTo X ⁻¹' U with hU'def
  have hU'o : IsOpen U' := hU.preimage (contDiff_restrictTo s X).continuous
  have hf : ContDiffOn ℝ 1 D.totalCost U' := by
    have h1 : ContDiffOn ℝ 1 (fun ξ => s.totalCost (s.restrictTo X ξ)) U' :=
      (hc.of_le (by norm_num)).comp ((contDiff_restrictTo s X).of_le (by norm_num)).contDiffOn
        (fun ξ hξ => hξ)
    have h2 : ContDiff ℝ 1 fun ξ : FreeCoords s.free => lam / 2 * ∑ b ∈ Finset.univ \ X, ‖ξ b‖ ^ 2 := by
      refine contDiff_const.mul (ContDiff.sum fun b _ => ?_)
      exact (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) b).norm_sq ℝ
    have h3 : D.totalCost = fun ξ => s.totalCost (s.restrictTo X ξ) +
        lam / 2 * ∑ b ∈ Finset.univ \ X, ‖ξ b‖ ^ 2 := by
      funext ξ
      exact restrictedSplit_totalCost s lam X ξ
    rw [h3]
    exact h1.add h2.contDiffOn
  have hftc := sum_integral_partial_eq_sub hU'o hf (η := η) fun v hv => hU' _ (hcut _ (hseg v hv))
  have hpsi : ∀ Y : TorusSite n, D.interaction Y η = R.coupling * (∑ b ∈ freeBondsAt s.free Y,
      ∫ v in (0 : ℝ)..1,
        deriv (fun τ : ℝ => D.totalCost (v • η + τ • (Pi.single b (η b) : TangentField s.free))) 0) -
        s.logJacobianAt Y (s.restrictTo X η) + s.logJacobianAt Y 0 := by
    intro Y
    show R.coupling * (∑ b ∈ freeBondsAt s.free Y, ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => D.totalCost (v • η + τ • singleBond b η)) 0) -
        s.logJacobianAt Y (s.restrictTo X η) + s.logJacobianAt Y (s.restrictTo X 0) = _
    simp only [singleBond_eq, restrictTo_zero]
  show ∑ Y : TorusSite n, D.interaction Y η = _
  simp only [hpsi]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_freeBondsAt s fun b => ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => D.totalCost (v • η + τ • (Pi.single b (η b) : TangentField s.free))) 0, hftc,
    restrictedSplit_totalCost, restrictedSplit_totalCost, restrictTo_zero, partPotential_zero_eq,
    partPotential_zero_eq]
  simp only [Pi.zero_apply, norm_zero]
  have h0 : ∑ b ∈ Finset.univ \ X, (0 : ℝ) ^ 2 = 0 := by simp
  rw [h0]
  ring
theorem coordNorm_lt_of_cutoffProduct_ne_zero {η : FreeCoords s.free} (h : s.cutoffProduct η ≠ 0) :
    ∀ b, coordNorm (η b) < R.ballRadius := by
  intro b
  have h1 : cutoffFactor R.ballRadius R.barrierFn (coordNorm (η b)) ≠ 0 := by
    intro h0
    exact h (Finset.prod_eq_zero (Finset.mem_univ b) h0)
  unfold cutoffFactor at h1
  by_contra hn
  exact h1 (if_neg hn)
theorem sum_gaussianPart (lam : ℝ) (η : FreeCoords s.free) :
    ∑ Y : TorusSite n, gaussianPart (R := R) lam Y η = R.coupling * lam / 2 * ∑ b, ‖η b‖ ^ 2 := by
  unfold gaussianPart
  rw [← Finset.mul_sum, sum_freeBondsAt s fun b => ‖η b‖ ^ 2]
theorem restrictedSplit_interpolatedDensity (lam τ : ℝ) (X : Finset s.free) {U : Set (FreeCoords s.free)}
    (hU : IsOpen U) (hU' : ∀ η, s.InBalls η → η ∈ U) (hc : ContDiffOn ℝ 3 s.totalCost U)
    (hρ : 0 ≤ R.ballRadius) (hcut : ∀ ξ, s.InBalls ξ → s.InBalls (s.restrictTo X ξ))
    (hconv : ∀ η, s.InBalls η → ∀ v ∈ Set.Icc (0 : ℝ) 1, s.InBalls (v • η)) (η : FreeCoords s.free) :
    (s.restrictedSplit lam X).interpolatedDensity lam τ η =
      Real.exp (τ * s.partPotential 0 0) *
        (s.cutoffProduct η * Real.exp (-s.cutGaussianMixPotential lam τ X η)) := by
  by_cases hz : s.cutoffProduct η = 0
  · show s.cutoffProduct η * _ = _
    rw [hz]
    simp
  · have hb : s.InBalls η := fun b => (coordNorm_lt_of_cutoffProduct_ne_zero s hz b).le
    have h1 := restrictedSplit_totalInteraction s lam X hU hU' hc hρ hb hcut (hconv η hb)
    show s.cutoffProduct η * Real.exp (-(τ * (s.restrictedSplit lam X).totalInteraction η) -
      (1 - τ) * ∑ Y : TorusSite n, gaussianPart lam Y η) = _
    rw [h1, sum_gaussianPart s]
    have he : -(τ * (s.partPotential 0 (s.restrictTo X η) + R.coupling * lam / 2 *
        ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2 - s.partPotential 0 0)) -
        (1 - τ) * (R.coupling * lam / 2 * ∑ b, ‖η b‖ ^ 2) =
        τ * s.partPotential 0 0 + -s.cutGaussianMixPotential lam τ X η := by
      unfold ChartSetting.cutGaussianMixPotential
      ring
    rw [he, Real.exp_add]
    ring
theorem weightedMean_const_mul_density {m : ℕ} {free : Finset (TorusBond m)} {d G : FreeCoords free → ℝ} {K : ℝ}
    (hK : 0 < K) :
    weightedMean (fun η => K * d η) G = weightedMean d G := by
  unfold weightedMean
  have h1 : ∫ η, G η * (K * d η) = K * ∫ η, G η * d η := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only
    ring
  rw [h1, integral_const_mul, mul_div_mul_left _ _ hK.ne']
theorem deriv_restrictedSplit_totalCost (lam : ℝ) (X : Finset s.free) {b : s.free} (hb : b ∈ X)
    {U : Set (FreeCoords s.free)} (hU : IsOpen U) (hc : ContDiffOn ℝ 3 s.totalCost U) {v : ℝ}
    {η : FreeCoords s.free} (hζ : v • s.restrictTo X η ∈ U) :
    deriv (fun τ : ℝ => (s.restrictedSplit lam X).totalCost
        (v • η + τ • (Pi.single b (η b) : TangentField s.free))) 0 =
      fderiv ℝ s.totalCost (v • s.restrictTo X η) (Pi.single b (η b) : TangentField s.free) := by
  classical
  have hdiff : DifferentiableAt ℝ s.totalCost (v • s.restrictTo X η) :=
    (hc.contDiffAt (hU.mem_nhds hζ)).differentiableAt (by norm_num)
  have h1 : (fun τ : ℝ => (s.restrictedSplit lam X).totalCost
        (v • η + τ • (Pi.single b (η b) : TangentField s.free))) =
      fun τ : ℝ => s.totalCost (v • s.restrictTo X η + τ • (Pi.single b (η b) : TangentField s.free)) +
        lam / 2 * ∑ c ∈ Finset.univ \ X, ‖(v • η) c‖ ^ 2 := by
    funext τ
    have e1 : s.restrictTo X (v • η + τ • (Pi.single b (η b) : TangentField s.free)) =
        v • s.restrictTo X η + τ • (Pi.single b (η b) : TangentField s.free) := by
      funext c
      unfold ChartSetting.restrictTo
      by_cases hcX : c ∈ X
      · simp [hcX]
      · have hcb : c ≠ b := fun h => hcX (h ▸ hb)
        simp [hcX, hcb]
    have e2 : ∑ c ∈ Finset.univ \ X, ‖(v • η + τ • (Pi.single b (η b) : TangentField s.free)) c‖ ^ 2 =
        ∑ c ∈ Finset.univ \ X, ‖(v • η) c‖ ^ 2 := by
      refine Finset.sum_congr rfl fun c hc' => ?_
      have hcX : c ∉ X := (Finset.mem_sdiff.mp hc').2
      have hcb : c ≠ b := fun h => hcX (h ▸ hb)
      simp [hcb]
    rw [restrictedSplit_totalCost, e1, e2]
  rw [h1]
  rw [deriv_add_const]
  exact deriv_line_eq_fderiv hdiff
theorem coordNorm_eq_norm (z : EuclideanSpace ℝ (Fin 3)) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
theorem convex_inBalls : Convex ℝ {ξ : FreeCoords s.free | s.InBalls ξ} := by
  intro ξ hξ ζ hζ a b ha hb hab c
  rw [coordNorm_eq_norm]
  have h1 := hξ c
  have h2 := hζ c
  rw [coordNorm_eq_norm] at h1 h2
  calc ‖(a • ξ + b • ζ) c‖ ≤ ‖a • ξ c‖ + ‖b • ζ c‖ := norm_add_le _ _
    _ = a * ‖ξ c‖ + b * ‖ζ c‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * R.ballRadius + b * R.ballRadius :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = R.ballRadius := by rw [← add_mul, hab, one_mul]
theorem inBalls_restrictTo (hρ : 0 ≤ R.ballRadius) (X : Finset s.free) (ξ : FreeCoords s.free)
    (h : s.InBalls ξ) : s.InBalls (s.restrictTo X ξ) := by
  intro b
  unfold ChartSetting.restrictTo
  split_ifs with hb
  · exact h b
  · rw [coordNorm_eq_norm, norm_zero]
    exact hρ
theorem inBalls_zero (hρ : 0 ≤ R.ballRadius) : s.InBalls (0 : FreeCoords s.free) := by
  intro b
  rw [Pi.zero_apply, coordNorm_eq_norm, norm_zero]
  exact hρ
theorem inBalls_smul (hρ : 0 ≤ R.ballRadius) (η : FreeCoords s.free) (h : s.InBalls η) (v : ℝ)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) : s.InBalls (v • η) := by
  have := convex_inBalls s (inBalls_zero s hρ) h (sub_nonneg.mpr hv.2) hv.1 (by ring)
  simpa using this
theorem abs_interaction_sub_gaussianPart_le (lam : ℝ) (hlam : 0 ≤ lam) (X : Finset s.free)
    {U : Set (FreeCoords s.free)} (hU : IsOpen U)
    (hU' : ∀ η, s.InBalls η → η ∈ U) (hc : ContDiffOn ℝ 3 s.totalCost U) (hρ : 0 ≤ R.ballRadius)
    (hx : 0 < R.coupling)
    {Y : TorusSite n} (hX : s.freeBondsOf Y ⊆ X) {M : s.free → s.free → ℝ} (hM0 : ∀ b b', 0 ≤ M b b')
    (hM : ∀ ξ, s.InBalls ξ → ∀ (b b' : s.free) (Z Z' : EuclideanSpace ℝ (Fin 3)), ‖Z‖ = 1 → ‖Z'‖ = 1 →
      |fderiv ℝ (fderiv ℝ s.totalCost) ξ (Pi.single b Z : TangentField s.free)
        (Pi.single b' Z' : TangentField s.free)| ≤ M b b')
    {J A₀ : ℝ} (hJ : ∀ ξ, s.InBalls ξ → |s.logJacobianAt Y ξ| ≤ J)
    (hA : ∀ b ∈ s.freeBondsOf Y, ∀ Z : EuclideanSpace ℝ (Fin 3),
      R.coupling * |fderiv ℝ s.totalCost 0 (Pi.single b Z : TangentField s.free)| ≤ A₀ * ‖Z‖)
    {η : FreeCoords s.free} (hη : s.InBalls η) :
    |(s.restrictedSplit lam X).interaction Y η - gaussianPart lam Y η| ≤
      2 * J + (∑ b ∈ freeBondsAt s.free Y, (A₀ * ‖η b‖ + R.coupling * ((∑ b', M b b' * ‖η b'‖) * ‖η b‖))) +
        gaussianPart lam Y η := by
  classical
  set D := s.restrictedSplit lam X with hD
  have hcf : ContDiffOn ℝ 2 s.totalCost U := hc.of_le (by norm_num)
  have hslope : ∀ b ∈ freeBondsAt s.free Y, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      R.coupling * |deriv (fun τ : ℝ => D.totalCost (v • η + τ • (Pi.single b (η b) : TangentField s.free))) 0| ≤
        A₀ * ‖η b‖ + R.coupling * ((∑ b', M b b' * ‖η b'‖) * ‖η b‖) := by
    intro b hb v hv
    have hζ : s.InBalls (v • s.restrictTo X η) :=
      inBalls_smul s hρ _ (inBalls_restrictTo s hρ X η hη) v hv
    rw [deriv_restrictedSplit_totalCost s lam X (hX hb) hU hc (hU' _ hζ)]
    have h1 := abs_fderiv_sub_le hU hcf (convex_inBalls s) (fun ξ hξ => hU' ξ hξ) (inBalls_zero s hρ)
      (fun ξ hξ b b' Z Z' hZ hZ' => hM ξ hξ b b' Z Z' hZ hZ') (ζ := v • s.restrictTo X η) hζ b (η b)
    have h2 : (∑ b', M b b' * ‖(v • s.restrictTo X η) b'‖) ≤ ∑ b', M b b' * ‖η b'‖ := by
      refine Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left ?_ (hM0 b b')
      have h3 : ‖(v • s.restrictTo X η) b'‖ = v * ‖s.restrictTo X η b'‖ := by
        rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1]
      have h4 : ‖s.restrictTo X η b'‖ ≤ ‖η b'‖ := by
        unfold ChartSetting.restrictTo
        split_ifs
        · exact le_rfl
        · rw [norm_zero]
          exact norm_nonneg _
      rw [h3]
      have := norm_nonneg (s.restrictTo X η b')
      nlinarith [hv.1, hv.2]
    have h5 := hA b hb (η b)
    have h6 : |fderiv ℝ s.totalCost (v • s.restrictTo X η) (Pi.single b (η b) : TangentField s.free)| ≤
        |fderiv ℝ s.totalCost (v • s.restrictTo X η) (Pi.single b (η b) : TangentField s.free) -
          fderiv ℝ s.totalCost 0 (Pi.single b (η b) : TangentField s.free)| +
        |fderiv ℝ s.totalCost 0 (Pi.single b (η b) : TangentField s.free)| := by
      have := abs_add_le (fderiv ℝ s.totalCost (v • s.restrictTo X η) (Pi.single b (η b) : TangentField s.free) -
          fderiv ℝ s.totalCost 0 (Pi.single b (η b) : TangentField s.free))
        (fderiv ℝ s.totalCost 0 (Pi.single b (η b) : TangentField s.free))
      simpa using this
    have h7 : (∑ b', M b b' * ‖(v • s.restrictTo X η) b'‖) * ‖η b‖ ≤ (∑ b', M b b' * ‖η b'‖) * ‖η b‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    calc R.coupling * |fderiv ℝ s.totalCost (v • s.restrictTo X η) (Pi.single b (η b) : TangentField s.free)|
        ≤ R.coupling * (((∑ b', M b b' * ‖(v • s.restrictTo X η) b'‖) * ‖η b‖) +
            |fderiv ℝ s.totalCost 0 (Pi.single b (η b) : TangentField s.free)|) :=
          mul_le_mul_of_nonneg_left (h6.trans (add_le_add_left h1 _)) hx.le
      _ ≤ _ := by nlinarith
  have hI : ∀ b ∈ freeBondsAt s.free Y,
      |R.coupling * ∫ v in (0 : ℝ)..1,
          deriv (fun τ : ℝ => D.totalCost (v • η + τ • (Pi.single b (η b) : TangentField s.free))) 0| ≤
        A₀ * ‖η b‖ + R.coupling * ((∑ b', M b b' * ‖η b'‖) * ‖η b‖) := by
    intro b hb
    have h1 : ‖∫ v in (0 : ℝ)..1,
          deriv (fun τ : ℝ => D.totalCost (v • η + τ • (Pi.single b (η b) : TangentField s.free))) 0‖ ≤
        (A₀ * ‖η b‖ + R.coupling * ((∑ b', M b b' * ‖η b'‖) * ‖η b‖)) / R.coupling * |(1 : ℝ) - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => ?_
      have hv' : v ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at hv
        exact ⟨hv.1.le, hv.2⟩
      rw [Real.norm_eq_abs, le_div_iff₀ hx, mul_comm]
      exact hslope b hb v hv'
    rw [abs_mul, abs_of_pos hx]
    rw [Real.norm_eq_abs] at h1
    simp only [sub_zero, abs_one, mul_one] at h1
    rw [le_div_iff₀ hx] at h1
    linarith
  have hpsi : D.interaction Y η = (∑ b ∈ freeBondsAt s.free Y, R.coupling * ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => D.totalCost (v • η + τ • (Pi.single b (η b) : TangentField s.free))) 0) -
        s.logJacobianAt Y (s.restrictTo X η) + s.logJacobianAt Y 0 := by
    show R.coupling * (∑ b ∈ freeBondsAt s.free Y, ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => D.totalCost (v • η + τ • singleBond b η)) 0) -
        s.logJacobianAt Y (s.restrictTo X η) + s.logJacobianAt Y (s.restrictTo X 0) = _
    simp only [singleBond_eq, restrictTo_zero, Finset.mul_sum]
  have hsum := (Finset.abs_sum_le_sum_abs (fun b => R.coupling * ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => D.totalCost (v • η + τ • (Pi.single b (η b) : TangentField s.free))) 0)
      (freeBondsAt s.free Y)).trans
    (Finset.sum_le_sum hI)
  have hj1 := hJ _ (inBalls_restrictTo s hρ X η hη)
  have hj2 := hJ _ (inBalls_zero s hρ)
  have hg : 0 ≤ gaussianPart (R := R) lam Y η := by
    unfold gaussianPart
    have : 0 ≤ ∑ b ∈ freeBondsAt s.free Y, ‖η b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    positivity
  rw [hpsi]
  rw [abs_le] at hj1 hj2 hsum ⊢
  constructor <;> linarith [hj1.1, hj1.2, hj2.1, hj2.2, hsum.1, hsum.2]
theorem inBalls_eq_pi : {ξ : FreeCoords s.free | s.InBalls ξ} =
    Set.univ.pi fun _ => Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R.ballRadius := by
  ext ξ
  simp [ChartSetting.InBalls, coordNorm_eq_norm, Set.mem_pi, mem_closedBall_zero_iff]
theorem isCompact_inBalls : IsCompact {ξ : FreeCoords s.free | s.InBalls ξ} := by
  rw [inBalls_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
theorem continuous_cutoffProduct (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (hrim : CutoffFactorIsRadialCutoff) : Continuous s.cutoffProduct := by
  have h1 : Continuous fun u : ℝ => cutoffFactor R.ballRadius R.barrierFn (max u 0) :=
    (hrim R.ballRadius R.barrierFn hρ hp).smooth.continuous
  have h2 : s.cutoffProduct = fun η => ∏ b : s.free, cutoffFactor R.ballRadius R.barrierFn (max ‖η b‖ 0) := by
    funext η
    unfold ChartSetting.cutoffProduct
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [coordNorm_eq_norm, max_eq_left (norm_nonneg _)]
  rw [h2]
  refine continuous_finset_prod _ fun b _ => ?_
  exact h1.comp (continuous_norm.comp (continuous_apply b))
theorem cutoffProduct_eq_zero {η : FreeCoords s.free} (h : ¬ s.InBalls η) : s.cutoffProduct η = 0 := by
  by_contra h0
  exact h fun b => (coordNorm_lt_of_cutoffProduct_ne_zero s h0 b).le
theorem cutoffProduct_nonneg (η : FreeCoords s.free) : 0 ≤ s.cutoffProduct η := by
  refine Finset.prod_nonneg fun b _ => ?_
  unfold cutoffFactor
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl
theorem integrable_mul_law (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (hrim : CutoffFactorIsRadialCutoff)
    {u f : FreeCoords s.free → ℝ} {U : Set (FreeCoords s.free)} (hU' : ∀ η, s.InBalls η → η ∈ U)
    (hu : ContinuousOn u U) (hf : Continuous f) :
    Integrable fun η => f η * (s.cutoffProduct η * Real.exp (-(u η))) := by
  have hK := isCompact_inBalls s
  have hc : ContinuousOn (fun η => f η * (s.cutoffProduct η * Real.exp (-(u η)))) {ξ | s.InBalls ξ} := by
    have h1 : ContinuousOn u {ξ | s.InBalls ξ} := hu.mono fun ξ hξ => hU' ξ hξ
    exact hf.continuousOn.mul ((continuous_cutoffProduct s hρ hp hrim).continuousOn.mul
      (Real.continuous_exp.comp_continuousOn h1.neg))
  have h2 := hc.integrableOn_compact (μ := volume) hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h2
  intro η hη
  by_contra hn
  apply hη
  show f η * (s.cutoffProduct η * _) = 0
  rw [cutoffProduct_eq_zero s hn]
  simp
end ChartSettings
section WeightedMeans
variable {m : ℕ} {free : Finset (TorusBond m)}
theorem weightedMean_add {d G H : FreeCoords free → ℝ} (hG : Integrable fun η => G η * d η)
    (hH : Integrable fun η => H η * d η) :
    weightedMean d (fun η => G η + H η) = weightedMean d G + weightedMean d H := by
  unfold weightedMean
  simp only [add_mul]
  rw [integral_add hG hH, add_div]
theorem weightedMean_const_mul {d G : FreeCoords free → ℝ} (a : ℝ) :
    weightedMean d (fun η => a * G η) = a * weightedMean d G := by
  unfold weightedMean
  simp only [mul_assoc]
  rw [integral_const_mul, mul_div_assoc]
theorem weightedMean_sum {ι' : Type} (S : Finset ι') {d : FreeCoords free → ℝ} {g : ι' → FreeCoords free → ℝ}
    (hg : ∀ i ∈ S, Integrable fun η => g i η * d η) :
    weightedMean d (fun η => ∑ i ∈ S, g i η) = ∑ i ∈ S, weightedMean d (g i) := by
  unfold weightedMean
  simp only [Finset.sum_mul]
  rw [integral_finset_sum S hg, Finset.sum_div]
theorem weightedMean_const {d : FreeCoords free → ℝ} (hd : 0 < ∫ η, d η) (c : ℝ) :
    weightedMean d (fun _ => c) = c := by
  unfold weightedMean
  rw [integral_const_mul, mul_div_assoc, div_self hd.ne', mul_one]
theorem abs_weightedMean_le {d G B : FreeCoords free → ℝ} (hd : ∀ η, 0 ≤ d η)
    (hB : Integrable fun η => B η * d η) (hbound : ∀ η, d η ≠ 0 → |G η| ≤ B η) (hpos : 0 < ∫ η, d η) :
    |weightedMean d G| ≤ weightedMean d B := by
  unfold weightedMean
  rw [abs_div, abs_of_pos hpos]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hB (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd η)]
  by_cases h : d η = 0
  · rw [h]
    simp
  · exact mul_le_mul_of_nonneg_right (hbound η h) (hd η)
theorem abs_weightedMean_le_of_quadratic {d G : FreeCoords free → ℝ} (hd : ∀ η, 0 ≤ d η)
    (hpos : 0 < ∫ η, d η)
    (hI : ∀ f : FreeCoords free → ℝ, Continuous f → Integrable fun η => f η * d η)
    {x lam J A₀ m₀ P Fr Bd : ℝ} (hx1 : 1 ≤ x) (hlam : 0 ≤ lam) (hA : 0 ≤ A₀) (hm0 : 0 ≤ m₀) (hP : 0 ≤ P)
    {FY Nr : Finset free} {M : free → free → ℝ} (hM0 : ∀ b b', 0 ≤ M b b')
    (hpoint : ∀ η, d η ≠ 0 → |G η| ≤ 2 * J +
      (∑ b ∈ FY, (A₀ * ‖η b‖ + x * ((∑ b', M b b' * ‖η b'‖) * ‖η b‖))) +
      x * lam / 2 * ∑ b ∈ FY, ‖η b‖ ^ 2)
    (hmom : ∀ b, weightedMean d (fun η => ‖η b‖ ^ 2) ≤ 1)
    (hnear : ∀ b ∈ Nr, weightedMean d (fun η => ‖η b‖ ^ 2) ≤ m₀ / x) (hFY : FY ⊆ Nr)
    (hPsum : ∀ b ∈ FY, ∑ b', M b b' ≤ P) (hFar : ∀ b ∈ FY, ∑ b' ∈ Finset.univ \ Nr, M b b' ≤ Fr)
    (hFr : 0 ≤ Fr) (hcard : (FY.card : ℝ) ≤ Bd) :
    |weightedMean d G| ≤ 2 * J + Bd * (A₀ ^ 2 / 2 + ((1 + lam) / 2 + P) * m₀ + x * Fr / 2) := by
  classical
  set c : free → ℝ := fun b => x / 2 * (1 + lam) + x / 2 * ∑ b', M b b' with hc
  set g : free → FreeCoords free → ℝ := fun b η =>
    A₀ ^ 2 / (2 * x) + (c b * ‖η b‖ ^ 2 + x / 2 * ∑ b', M b b' * ‖η b'‖ ^ 2) with hg
  have hcont : ∀ b : free, Continuous fun η : FreeCoords free => ‖η b‖ ^ 2 := fun b =>
    (continuous_norm.comp (continuous_apply b)).pow 2
  have hgc : ∀ b, Continuous (g b) := by
    intro b
    refine continuous_const.add ((continuous_const.mul (hcont b)).add (continuous_const.mul ?_))
    exact continuous_finset_sum _ fun b' _ => continuous_const.mul (hcont b')
  have hbd : ∀ η, d η ≠ 0 → |G η| ≤ 2 * J + ∑ b ∈ FY, g b η := by
    intro η hη
    refine (hpoint η hη).trans ?_
    have h1 : ∀ b ∈ FY, A₀ * ‖η b‖ + x * ((∑ b', M b b' * ‖η b'‖) * ‖η b‖) + x * lam / 2 * ‖η b‖ ^ 2 ≤
        g b η := by
      intro b _
      set t := ‖η b‖ with ht
      have e1 : A₀ * t ≤ A₀ ^ 2 / (2 * x) + x / 2 * t ^ 2 := by
        rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (A₀ - x * t)]
      have e2 : x * ((∑ b', M b b' * ‖η b'‖) * t) ≤
          x / 2 * ∑ b', M b b' * ‖η b'‖ ^ 2 + x / 2 * (∑ b', M b b') * t ^ 2 := by
        have : (∑ b', M b b' * ‖η b'‖) * t ≤
            (1 / 2) * ∑ b', M b b' * ‖η b'‖ ^ 2 + (1 / 2) * (∑ b', M b b') * t ^ 2 := by
          rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun b' _ => ?_
          have := mul_nonneg (hM0 b b') (sq_nonneg (‖η b'‖ - t))
          nlinarith
        nlinarith
      show _ ≤ A₀ ^ 2 / (2 * x) + ((x / 2 * (1 + lam) + x / 2 * ∑ b', M b b') * t ^ 2 +
        x / 2 * ∑ b', M b b' * ‖η b'‖ ^ 2)
      nlinarith
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
    linarith
  have hBc : Continuous fun η => 2 * J + ∑ b ∈ FY, g b η :=
    continuous_const.add (continuous_finset_sum _ fun b _ => hgc b)
  have h1 := abs_weightedMean_le hd (hI _ hBc) hbd hpos
  have hmean_g : ∀ b, weightedMean d (g b) = A₀ ^ 2 / (2 * x) + (c b * weightedMean d (fun η => ‖η b‖ ^ 2) +
      x / 2 * ∑ b', M b b' * weightedMean d (fun η => ‖η b'‖ ^ 2)) := by
    intro b
    have e1 : weightedMean d (g b) = weightedMean d (fun _ => A₀ ^ 2 / (2 * x)) +
        weightedMean d (fun η => c b * ‖η b‖ ^ 2 + x / 2 * ∑ b', M b b' * ‖η b'‖ ^ 2) :=
      weightedMean_add (hI _ continuous_const) (hI _ ((continuous_const.mul (hcont b)).add
        (continuous_const.mul (continuous_finset_sum _ fun b' _ => continuous_const.mul (hcont b')))))
    have e2 : weightedMean d (fun η => c b * ‖η b‖ ^ 2 + x / 2 * ∑ b', M b b' * ‖η b'‖ ^ 2) =
        weightedMean d (fun η => c b * ‖η b‖ ^ 2) +
          weightedMean d (fun η => x / 2 * ∑ b', M b b' * ‖η b'‖ ^ 2) :=
      weightedMean_add (hI _ (continuous_const.mul (hcont b)))
        (hI _ (continuous_const.mul (continuous_finset_sum _ fun b' _ => continuous_const.mul (hcont b'))))
    have e3 : weightedMean d (fun η => ∑ b', M b b' * ‖η b'‖ ^ 2) =
        ∑ b', M b b' * weightedMean d (fun η => ‖η b'‖ ^ 2) := by
      have e4 := weightedMean_sum (d := d) (Finset.univ : Finset free) (g := fun b' η => M b b' * ‖η b'‖ ^ 2)
        (fun b' _ => hI _ (continuous_const.mul (hcont b')))
      rw [e4]
      exact Finset.sum_congr rfl fun b' _ => weightedMean_const_mul _
    rw [e1, e2, weightedMean_const hpos, weightedMean_const_mul, weightedMean_const_mul, e3]
  have hmeanB : weightedMean d (fun η => 2 * J + ∑ b ∈ FY, g b η) =
      2 * J + ∑ b ∈ FY, weightedMean d (g b) := by
    rw [weightedMean_add (hI _ continuous_const) (hI _ (continuous_finset_sum _ fun b _ => hgc b)),
      weightedMean_const hpos, weightedMean_sum _ fun b _ => hI _ (hgc b)]
  have hone : ∀ b ∈ FY, weightedMean d (g b) ≤ A₀ ^ 2 / 2 + ((1 + lam) / 2 + P) * m₀ + x * Fr / 2 := by
    intro b hb
    rw [hmean_g]
    have hnb := hnear b (hFY hb)
    have hP1 := hPsum b hb
    have hsum0 : 0 ≤ ∑ b', M b b' := Finset.sum_nonneg fun b' _ => hM0 b b'
    have e1 : A₀ ^ 2 / (2 * x) ≤ A₀ ^ 2 / 2 := by
      refine div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
    have hc0 : 0 ≤ c b := by positivity
    have e2 : c b * weightedMean d (fun η => ‖η b‖ ^ 2) ≤ ((1 + lam) / 2 + P / 2) * m₀ := by
      refine (mul_le_mul_of_nonneg_left hnb hc0).trans ?_
      have : c b * (m₀ / x) = ((1 + lam) / 2 + (∑ b', M b b') / 2) * m₀ := by
        show (x / 2 * (1 + lam) + x / 2 * ∑ b', M b b') * (m₀ / x) = _
        field_simp
      rw [this]
      nlinarith
    have e3 : ∑ b', M b b' * weightedMean d (fun η => ‖η b'‖ ^ 2) ≤
        (∑ b', M b b') * (m₀ / x) + Fr := by
      have hsplit : ∑ b', M b b' * weightedMean d (fun η => ‖η b'‖ ^ 2) =
          ∑ b' ∈ Nr, M b b' * weightedMean d (fun η => ‖η b'‖ ^ 2) +
            ∑ b' ∈ Finset.univ \ Nr, M b b' * weightedMean d (fun η => ‖η b'‖ ^ 2) := by
        rw [add_comm, Finset.sum_sdiff (Finset.subset_univ Nr)]
      have hA1 : ∑ b' ∈ Nr, M b b' * weightedMean d (fun η => ‖η b'‖ ^ 2) ≤ (∑ b', M b b') * (m₀ / x) := by
        calc _ ≤ ∑ b' ∈ Nr, M b b' * (m₀ / x) :=
              Finset.sum_le_sum fun b' hb' => mul_le_mul_of_nonneg_left (hnear b' hb') (hM0 b b')
          _ = (∑ b' ∈ Nr, M b b') * (m₀ / x) := by rw [Finset.sum_mul]
          _ ≤ _ := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b' _ _ => hM0 b b'
      have hB1 : ∑ b' ∈ Finset.univ \ Nr, M b b' * weightedMean d (fun η => ‖η b'‖ ^ 2) ≤ Fr := by
        calc _ ≤ ∑ b' ∈ Finset.univ \ Nr, M b b' * 1 :=
              Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left (hmom b') (hM0 b b')
          _ ≤ Fr := by simpa using hFar b hb
      rw [hsplit]
      linarith
    have e4 : x / 2 * ∑ b', M b b' * weightedMean d (fun η => ‖η b'‖ ^ 2) ≤ P / 2 * m₀ + x * Fr / 2 := by
      have h3 := mul_le_mul_of_nonneg_left e3 (by positivity : 0 ≤ x / 2)
      have h4 : x / 2 * ((∑ b', M b b') * (m₀ / x) + Fr) = (∑ b', M b b') / 2 * m₀ + x * Fr / 2 := by
        field_simp
      rw [h4] at h3
      nlinarith
    nlinarith
  have hQ0 : 0 ≤ A₀ ^ 2 / 2 + ((1 + lam) / 2 + P) * m₀ + x * Fr / 2 := by positivity
  calc |weightedMean d G| ≤ weightedMean d (fun η => 2 * J + ∑ b ∈ FY, g b η) := h1
    _ = 2 * J + ∑ b ∈ FY, weightedMean d (g b) := hmeanB
    _ ≤ 2 * J + ∑ _b ∈ FY, (A₀ ^ 2 / 2 + ((1 + lam) / 2 + P) * m₀ + x * Fr / 2) := by
        linarith [Finset.sum_le_sum hone]
    _ = 2 * J + (FY.card : ℝ) * (A₀ ^ 2 / 2 + ((1 + lam) / 2 + P) * m₀ + x * Fr / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by nlinarith
end WeightedMeans
section Estimates
variable {R : StepSetup} {n : ℕ} [NeZero n] (s : ChartSetting R n)
theorem update_zero_smul_eq (b : s.free) (Z : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    Function.update (0 : FreeCoords s.free) b (t • Z) =
      (0 : FreeCoords s.free) + t • (Pi.single b Z : TangentField s.free) := by
  have := update_add_smul_eq (0 : FreeCoords s.free) b Z t
  simpa using this
theorem deriv_partPotential_line {b : s.free} {Z : EuclideanSpace ℝ (Fin 3)} {U : Set (FreeCoords s.free)}
    (hU : IsOpen U) (h0 : (0 : FreeCoords s.free) ∈ U) (hc : ContDiffOn ℝ 3 s.totalCost U)
    (hu : ContDiffOn ℝ 3 (s.partPotential 0) U) :
    deriv (fun t : ℝ => s.partPotential 0 (Function.update 0 b (t • Z))) 0 =
      R.coupling * deriv (fun t : ℝ => s.totalCost (Function.update 0 b (t • Z))) 0 -
        deriv (fun t : ℝ => ∑ Y : TorusSite n, s.logJacobianAt Y (Function.update 0 b (t • Z))) 0 := by
  have hline : HasDerivAt (fun t : ℝ => (0 : FreeCoords s.free) + t • (Pi.single b Z : TangentField s.free))
      (Pi.single b Z : TangentField s.free) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single b Z : TangentField s.free)).const_add
      (0 : FreeCoords s.free)
  have hdc : DifferentiableAt ℝ s.totalCost 0 :=
    (hc.contDiffAt (hU.mem_nhds h0)).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ (s.partPotential 0) 0 :=
    (hu.contDiffAt (hU.mem_nhds h0)).differentiableAt (by norm_num)
  have e1 : DifferentiableAt ℝ (fun t : ℝ => s.totalCost (Function.update 0 b (t • Z))) 0 := by
    simp only [update_zero_smul_eq]
    exact (HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdc.hasFDerivAt hline (by simp)).differentiableAt
  have e2 : DifferentiableAt ℝ (fun t : ℝ => s.partPotential 0 (Function.update 0 b (t • Z))) 0 := by
    simp only [update_zero_smul_eq]
    exact (HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdu.hasFDerivAt hline (by simp)).differentiableAt
  have hj : (fun t : ℝ => ∑ Y : TorusSite n, s.logJacobianAt Y (Function.update 0 b (t • Z))) =
      fun t => R.coupling * s.totalCost (Function.update 0 b (t • Z)) -
        s.partPotential 0 (Function.update 0 b (t • Z)) := by
    funext t
    rw [partPotential_zero_eq]
    ring
  rw [hj, deriv_fun_sub (e1.const_mul _) e2, deriv_const_mul _ e1]
  ring
theorem abs_partialSlope_mix_le {lam τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (X : Finset s.free) {b : s.free}
    {Z : EuclideanSpace ℝ (Fin 3)} (hZ : ‖Z‖ = 1) {A : ℝ} (hA0 : 0 ≤ A)
    (hd : DifferentiableAt ℝ (fun t : ℝ => s.partPotential 0 (Function.update 0 b (t • Z))) 0)
    (hA : |deriv (fun t : ℝ => s.partPotential 0 (Function.update 0 b (t • Z))) 0| ≤ A) :
    |partialSlope (s.cutGaussianMixPotential lam τ X) 0 b Z| ≤ A := by
  classical
  have hall : ∀ t : ℝ, ∑ c, ‖(Function.update (0 : FreeCoords s.free) b (t • Z)) c‖ ^ 2 = t ^ 2 := by
    intro t
    rw [Finset.sum_eq_single b]
    · simp [norm_smul, hZ]
    · intro c _ hc
      simp [hc]
    · simp
  unfold partialSlope
  simp only [Pi.zero_apply, zero_add]
  by_cases hb : b ∈ X
  · have hfun : (fun t : ℝ => s.cutGaussianMixPotential lam τ X (Function.update 0 b (t • Z))) =
        fun t => τ * s.partPotential 0 (Function.update 0 b (t • Z)) + (1 - τ) * (R.coupling * lam / 2) * t ^ 2 := by
      funext t
      unfold ChartSetting.cutGaussianMixPotential
      have e1 : s.restrictTo X (Function.update (0 : FreeCoords s.free) b (t • Z)) =
          Function.update (0 : FreeCoords s.free) b (t • Z) := by
        funext c
        unfold ChartSetting.restrictTo
        by_cases hcb : c = b
        · subst hcb
          simp [hb]
        · by_cases hcX : c ∈ X
          · simp [hcX]
          · simp [hcX, hcb]
      have e2 : ∑ c ∈ Finset.univ \ X, ‖(Function.update (0 : FreeCoords s.free) b (t • Z)) c‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun c hc => ?_
        have hcb : c ≠ b := fun h => (Finset.mem_sdiff.mp hc).2 (h ▸ hb)
        simp [hcb]
      rw [e1, e2, hall]
      ring
    rw [hfun]
    have hq : DifferentiableAt ℝ (fun t : ℝ => (1 - τ) * (R.coupling * lam / 2) * t ^ 2) 0 := by fun_prop
    rw [deriv_fun_add (hd.const_mul _) hq, deriv_const_mul _ hd]
    have hq0 : deriv (fun t : ℝ => (1 - τ) * (R.coupling * lam / 2) * t ^ 2) 0 = 0 := by
      simp [deriv_const_mul]
    rw [hq0, add_zero, abs_mul, abs_of_nonneg hτ0]
    nlinarith [abs_nonneg (deriv (fun t : ℝ => s.partPotential 0 (Function.update 0 b (t • Z))) 0)]
  · have hfun : (fun t : ℝ => s.cutGaussianMixPotential lam τ X (Function.update 0 b (t • Z))) =
        fun t => τ * s.partPotential 0 0 + (R.coupling * lam / 2) * t ^ 2 := by
      funext t
      unfold ChartSetting.cutGaussianMixPotential
      have e1 : s.restrictTo X (Function.update (0 : FreeCoords s.free) b (t • Z)) = 0 := by
        funext c
        unfold ChartSetting.restrictTo
        by_cases hcX : c ∈ X
        · have hcb : c ≠ b := fun h => hb (h ▸ hcX)
          simp [hcX, hcb]
        · simp [hcX]
      have e2 : ∑ c ∈ Finset.univ \ X, ‖(Function.update (0 : FreeCoords s.free) b (t • Z)) c‖ ^ 2 = t ^ 2 := by
        rw [Finset.sum_eq_single b]
        · simp [norm_smul, hZ]
        · intro c _ hc
          simp [hc]
        · intro h
          exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hb⟩) h
      rw [e1, e2, hall]
      ring
    rw [hfun]
    have hq : deriv (fun t : ℝ => τ * s.partPotential 0 0 + (R.coupling * lam / 2) * t ^ 2) 0 = 0 := by
      simp [deriv_const_mul]
    rw [hq, abs_zero]
    exact hA0
theorem card_bondBlock_le (hBd : BondsPerBlockBound) (Z : TorusSite n) :
    (((Finset.univ : Finset s.free).filter fun b => bondBlock (R := R) b.1 = Z).card : ℝ) ≤
      R.params.blockBondBound := by
  classical
  have h1 := hBd R.params.side n Z
  refine le_trans ?_ h1
  have h2 : ((Finset.univ : Finset s.free).filter fun b => bondBlock (R := R) b.1 = Z).card ≤
      ((Finset.univ : Finset (TorusBond (n * R.params.side))).filter
        fun b => parentBlock R.params.side b.1 = Z).card := by
    refine Finset.card_le_card_of_injOn (fun b => b.1) ?_ ?_
    · intro b hb
      have : bondBlock (R := R) b.1 = Z := by simpa using hb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact this
    · intro b _ b' _ h
      exact Subtype.ext h
  exact_mod_cast h2
theorem sum_exp_far_bonds_le {Bd c A : ℝ} (hBd : ∀ Z : TorusSite n,
      (((Finset.univ : Finset s.free).filter fun b => bondBlock (R := R) b.1 = Z).card : ℝ) ≤ Bd)
    (hA : ∀ (y : TorusSite n) (D' : ℕ), ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D' ≤ supDist Y y),
      Real.exp (-(c * supDist Y y)) ≤ A * Real.exp (-(c * D' / 2)))
    (y : TorusSite n) (D' : ℕ) (hBd0 : 0 ≤ Bd) :
    ∑ b ∈ (Finset.univ : Finset s.free).filter (fun b => D' ≤ supDist (bondBlock (R := R) b.1) y),
      Real.exp (-(c * supDist (bondBlock (R := R) b.1) y)) ≤ Bd * (A * Real.exp (-(c * D' / 2))) := by
  classical
  set S := (Finset.univ : Finset s.free).filter (fun b => D' ≤ supDist (bondBlock (R := R) b.1) y) with hS
  set t := Finset.univ.filter (fun Y : TorusSite n => D' ≤ supDist Y y) with ht
  have hmaps : ∀ b ∈ S, bondBlock (R := R) b.1 ∈ t := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hin : ∀ Z ∈ t, ∑ b ∈ S with bondBlock (R := R) b.1 = Z,
      Real.exp (-(c * supDist (bondBlock (R := R) b.1) y)) ≤ Bd * Real.exp (-(c * supDist Z y)) := by
    intro Z _
    have h1 : ∑ b ∈ S with bondBlock (R := R) b.1 = Z, Real.exp (-(c * supDist (bondBlock (R := R) b.1) y)) =
        ∑ b ∈ S.filter (fun b => bondBlock (R := R) b.1 = Z), Real.exp (-(c * supDist Z y)) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [(Finset.mem_filter.mp hb).2]
    rw [h1, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine le_trans ?_ (hBd Z)
    have h2 : (S.filter fun b => bondBlock (R := R) b.1 = Z) ⊆
        (Finset.univ : Finset s.free).filter fun b => bondBlock (R := R) b.1 = Z := by
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
    exact_mod_cast Finset.card_le_card h2
  refine (Finset.sum_le_sum hin).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hA y D') hBd0
theorem sum_row_le {M : s.free → s.free → ℝ} {rt lam Ch Bd : ℝ} (hrt : 0 < rt) (hM0 : ∀ b b', 0 ≤ M b b')
    (hMC : ∀ b b', M b b' ≤ Ch) (hCh : 0 ≤ Ch)
    (hrows : ∀ b, ∑ b', M b b' * (Real.exp (2 * rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) ≤ lam / 16)
    (hBd : ∀ Z : TorusSite n,
      (((Finset.univ : Finset s.free).filter fun b => bondBlock (R := R) b.1 = Z).card : ℝ) ≤ Bd) (b : s.free) :
    ∑ b', M b b' ≤ Ch * Bd + lam / 16 / (2 * rt) := by
  classical
  have hterm : ∀ b' : s.free, M b b' ≤ (if bondBlock (R := R) b'.1 = bondBlock (R := R) b.1 then Ch else 0) +
      M b b' * (Real.exp (2 * rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) / (2 * rt) := by
    intro b'
    have hE : 0 ≤ Real.exp (2 * rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1 := by
      have := Real.one_le_exp (by positivity : 0 ≤ 2 * rt * (bondBlockDist (R := R) (n := n) b.1 b'.1 : ℝ))
      linarith
    split_ifs with h
    · have : 0 ≤ M b b' * (Real.exp (2 * rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) / (2 * rt) :=
        div_nonneg (mul_nonneg (hM0 b b') hE) (by positivity)
      linarith [hMC b b']
    · have hd : 1 ≤ bondBlockDist (R := R) (n := n) b.1 b'.1 := by
        by_contra h0
        have h1 : supDist (bondBlock (R := R) b.1) (bondBlock (R := R) b'.1) = 0 := by
          unfold bondBlockDist at h0
          omega
        have h2 := (supDist_le_iff _ _ 0).mp h1.le
        apply h
        funext i
        have h3 := h2 i
        have h4 : ((bondBlock (R := R) b.1 i - bondBlock (R := R) b'.1 i).valMinAbs) = 0 := by
          simpa using h3
        have h5 := (ZMod.valMinAbs_eq_zero _).mp h4
        exact (sub_eq_zero.mp h5).symm
      have h2 : (2 * rt) ≤ Real.exp (2 * rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1 := by
        have h3 := Real.add_one_le_exp (2 * rt * (bondBlockDist (R := R) (n := n) b.1 b'.1 : ℝ))
        have h4 : (1 : ℝ) ≤ bondBlockDist (R := R) (n := n) b.1 b'.1 := by exact_mod_cast hd
        nlinarith
      rw [zero_add, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left h2 (hM0 b b')
  refine (Finset.sum_le_sum fun b' _ => hterm b').trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  have h1 : ∑ b' : s.free, (if bondBlock (R := R) b'.1 = bondBlock (R := R) b.1 then Ch else 0) ≤ Ch * Bd := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hBd _) hCh
  have h2 := div_le_div_of_nonneg_right (hrows b) (by positivity : 0 ≤ 2 * rt)
  linarith
theorem sum_row_far_le {M : s.free → s.free → ℝ} {rt lam x : ℝ} (hrt : 0 < rt) (hM0 : ∀ b b', 0 ≤ M b b')
    (hx : 0 < x) (hlam : 0 ≤ lam)
    (hrows : ∀ b, ∑ b', M b b' * (Real.exp (2 * rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) ≤ lam / 16)
    {b : s.free} {Nr : Finset s.free} {D : ℕ}
    (hfar : ∀ b' ∈ Finset.univ \ Nr, D ≤ bondBlockDist (R := R) (n := n) b.1 b'.1)
    (hE : x ≤ Real.exp (2 * rt * D) - 1) :
    ∑ b' ∈ Finset.univ \ Nr, M b b' ≤ lam / 16 / x := by
  rw [le_div_iff₀ hx, Finset.sum_mul]
  have hstep : ∀ b' ∈ Finset.univ \ Nr, M b b' * x ≤
      M b b' * (Real.exp (2 * rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) := by
    intro b' hb'
    refine mul_le_mul_of_nonneg_left (hE.trans ?_) (hM0 b b')
    have h1 : (D : ℝ) ≤ bondBlockDist (R := R) (n := n) b.1 b'.1 := by exact_mod_cast hfar b' hb'
    have h2 : Real.exp (2 * rt * D) ≤ Real.exp (2 * rt * bondBlockDist (R := R) (n := n) b.1 b'.1) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  refine (Finset.sum_le_sum hstep).trans ?_
  refine le_trans ?_ (hrows b)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b' _ _ => ?_
  refine mul_nonneg (hM0 b b') ?_
  have := Real.one_le_exp (by positivity : 0 ≤ 2 * rt * (bondBlockDist (R := R) (n := n) b.1 b'.1 : ℝ))
  linarith
theorem moment_le_of_slopes {x CF A₁ Cu W Fw m : ℝ} (hx1 : 1 ≤ x) (hCF : 0 ≤ CF) {Near : Finset s.free}
    {e : s.free → ℝ} (he : ∀ b, 0 ≤ e b) (hW : ∑ b', e b' ≤ W) (hF : ∑ b' ∈ Finset.univ \ Near, e b' ≤ Fw)
    (hq : x * Fw ≤ 1)
    (hfact : m ≤ CF / x + CF / x ^ 2 * ∑ b', e b' * (if b' ∈ Near then A₁ else Cu * x) ^ 2) :
    m ≤ (CF + CF * A₁ ^ 2 * W + CF * Cu ^ 2) / x := by
  classical
  have hx : 0 < x := by linarith
  have hsum : ∑ b', e b' * (if b' ∈ Near then A₁ else Cu * x) ^ 2 ≤ A₁ ^ 2 * W + (Cu * x) ^ 2 * Fw := by
    have h1 : ∀ b' : s.free, e b' * (if b' ∈ Near then A₁ else Cu * x) ^ 2 ≤
        A₁ ^ 2 * e b' + (Cu * x) ^ 2 * (if b' ∈ Near then 0 else e b') := by
      intro b'
      split_ifs
      · nlinarith
      · nlinarith [mul_nonneg (sq_nonneg A₁) (he b')]
    refine (Finset.sum_le_sum fun b' _ => h1 b').trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h2 : ∑ b', (if b' ∈ Near then 0 else e b') ≤ Fw := by
      refine le_trans (le_of_eq ?_) hF
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext b'
      simp [Finset.mem_sdiff, Finset.mem_filter]
    exact add_le_add (mul_le_mul_of_nonneg_left hW (sq_nonneg _))
      (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
  refine hfact.trans ?_
  have h3 : CF / x ^ 2 * ∑ b', e b' * (if b' ∈ Near then A₁ else Cu * x) ^ 2 ≤
      CF / x ^ 2 * (A₁ ^ 2 * W + (Cu * x) ^ 2 * Fw) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hW0 : 0 ≤ W := le_trans (Finset.sum_nonneg fun b _ => he b) hW
  have h4 : CF / x ^ 2 * (A₁ ^ 2 * W + (Cu * x) ^ 2 * Fw) ≤ (CF * A₁ ^ 2 * W + CF * Cu ^ 2) / x := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hx]
    have h5 : 0 ≤ CF * A₁ ^ 2 * W := by positivity
    have h6 : CF * Cu ^ 2 * (x ^ 2 * (x * Fw)) ≤ CF * Cu ^ 2 * (x ^ 2 * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by positivity)) (by positivity)
    nlinarith [mul_nonneg h5 (sub_nonneg.mpr hx1), mul_nonneg h5 hx.le]
  have h7 : CF / x + (CF * A₁ ^ 2 * W + CF * Cu ^ 2) / x = (CF + CF * A₁ ^ 2 * W + CF * Cu ^ 2) / x := by
    field_simp
    ring
  linarith
theorem div_le_supDist_of_far {Y : TorusSite n} {b b' : s.free} {L r : ℕ} (hL : 0 < L)
    (h1 : (32 * L : ℝ) * supDist (bondBlock (R := R) b.1) Y ≤ r)
    (h2 : ¬ (16 * L : ℝ) * supDist (bondBlock (R := R) b'.1) Y ≤ r) :
    r / (32 * L) ≤ supDist (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1) := by
  have ht := supDist_triangle (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1) Y
  have ht' : (supDist (bondBlock (R := R) b'.1) Y : ℝ) ≤
      supDist (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1) + supDist (bondBlock (R := R) b.1) Y := by
    exact_mod_cast ht
  rw [not_le] at h2
  have h3 : (r : ℝ) ≤ (32 * L : ℝ) * supDist (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1) := by
    nlinarith
  have h4 : r ≤ 32 * L * supDist (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1) := by exact_mod_cast h3
  exact Nat.div_le_of_le_mul h4
theorem div_le_supDist_of_not_le {Y : TorusSite n} {b' : s.free} {L r : ℕ}
    (h2 : ¬ (32 * L : ℝ) * supDist (bondBlock (R := R) b'.1) Y ≤ r) :
    r / (32 * L) ≤ supDist (bondBlock (R := R) b'.1) Y := by
  rw [not_le] at h2
  have h4 : r ≤ 32 * L * supDist (bondBlock (R := R) b'.1) Y := by
    have : (r : ℝ) ≤ (32 * L : ℝ) * supDist (bondBlock (R := R) b'.1) Y := h2.le
    exact_mod_cast this
  exact Nat.div_le_of_le_mul h4
theorem integral_cutoff_law_pos (hρ : 0 < R.ballRadius) {u : FreeCoords s.free → ℝ}
    (hI : Integrable fun η => s.cutoffProduct η * Real.exp (-(u η))) :
    0 < ∫ η, s.cutoffProduct η * Real.exp (-(u η)) := by
  have hd : ∀ η, 0 ≤ s.cutoffProduct η * Real.exp (-(u η)) := fun η =>
    mul_nonneg (cutoffProduct_nonneg s η) (Real.exp_pos _).le
  rw [integral_pos_iff_support_of_nonneg hd hI]
  set O : Set (FreeCoords s.free) := {η | ∀ b, ‖η b‖ < R.ballRadius} with hO
  have hOo : IsOpen O := by
    have : O = ⋂ b, {η : FreeCoords s.free | ‖η b‖ < R.ballRadius} := by
      ext η
      simp [hO]
    rw [this]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have h0 : (0 : FreeCoords s.free) ∈ O := fun b => by simpa using hρ
  have hsub : O ⊆ Function.support fun η => s.cutoffProduct η * Real.exp (-(u η)) := by
    intro η hη
    refine mul_ne_zero ?_ (Real.exp_pos _).ne'
    refine (Finset.prod_pos fun b _ => ?_).ne'
    unfold cutoffFactor
    rw [if_pos (by rw [coordNorm_eq_norm]; exact hη b)]
    exact Real.exp_pos _
  exact lt_of_lt_of_le (hOo.measure_pos volume ⟨0, h0⟩) (measure_mono hsub)
set_option maxHeartbeats 2000000 in
theorem abs_weightedMean_gain_le {lam τ : ℝ} (hlam : 0 < lam) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (X : Finset s.free)
    {Y : TorusSite n} (hX : s.freeBondsOf Y ⊆ X) (hρ0 : 0 < R.ballRadius) (hρ1 : R.ballRadius ≤ 1)
    (hp : IsCutoff R.ballRadius R.barrierFn) (hrim : CutoffFactorIsRadialCutoff)
    (hx2 : 2 ≤ R.coupling) (hrt : 0 < R.params.rt) {Cu Ch C3 CJ J CF W Bd As : ℝ} (hCu : 0 ≤ Cu)
    (hCh : 0 ≤ Ch) (hC3 : 0 ≤ C3)
    (hCJ : 0 ≤ CJ) (hCF : 0 ≤ CF) (hBd0 : 0 ≤ Bd) (hW0 : 0 ≤ W)
    (hcr : s.HasCostDecay lam Ch) (hpart : s.HasFullDecay (s.partPotential 0) lam Cu)
    (hmix : s.HasFullDecay (s.cutGaussianMixPotential lam τ X) lam Cu)
    (hfact : ∀ A : s.free → ℝ,
      (∀ b Z, ‖Z‖ = 1 → |partialSlope (s.cutGaussianMixPotential lam τ X) 0 b Z| ≤ A b) → ∀ b,
      weightedMean (fun η => s.cutoffProduct η * Real.exp (-(s.cutGaussianMixPotential lam τ X η)))
          (fun η => ‖η b‖ ^ 2) ≤
        CF / R.coupling + CF / R.coupling ^ 2 *
          ∑ b', Real.exp (-(2 * R.params.rt * s.bondDist b b')) * A b' ^ 2)
    (hW : ∀ b₀ : s.free, ∑ b, Real.exp (-(2 * R.params.rt * s.bondDist b b₀)) ≤ W)
    (hBd : ∀ Z : TorusSite n,
      (((Finset.univ : Finset s.free).filter fun b => bondBlock (R := R) b.1 = Z).card : ℝ) ≤ Bd)
    (hAs : ∀ (y : TorusSite n) (D' : ℕ), ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D' ≤ supDist Y y),
      Real.exp (-(2 * R.params.rt * supDist Y y)) ≤ As * Real.exp (-(2 * R.params.rt * D' / 2)))
    (hS3 : ∀ (b : s.free) (Z : EuclideanSpace ℝ (Fin 3)), ‖Z‖ = 1 →
      (16 * R.params.side : ℝ) * supDist (bondBlock (R := R) b.1) Y ≤ R.range →
      R.coupling * |deriv (fun t : ℝ => s.totalCost (Function.update 0 b (t • Z))) 0| ≤ C3)
    (hSJ : ∀ (b : s.free) (Z : EuclideanSpace ℝ (Fin 3)), ‖Z‖ = 1 →
      |deriv (fun t : ℝ => ∑ Y : TorusSite n, s.logJacobianAt Y (Function.update 0 b (t • Z))) 0| ≤ CJ)
    (hJ : ∀ ξ, s.InBalls ξ → |s.logJacobianAt Y ξ| ≤ J)
    (hq1 : R.coupling * (Bd * (As * Real.exp (-(2 * R.params.rt *
      ((R.range / (32 * R.params.side) : ℕ) : ℝ) / 2)))) ≤ 1)
    (hq2 : R.coupling ≤ Real.exp (2 * R.params.rt * ((R.range / (32 * R.params.side) : ℕ) : ℝ)) - 1) :
    |weightedMean ((s.restrictedSplit lam X).interpolatedDensity lam τ)
        (fun η => (s.restrictedSplit lam X).interaction Y η - gaussianPart lam Y η)| ≤
      2 * J + Bd * (C3 ^ 2 / 2 + ((1 + lam) / 2 + (Ch * Bd + lam / 16 / (2 * R.params.rt))) *
        (CF + CF * (C3 + CJ) ^ 2 * W + CF * Cu ^ 2) + R.coupling * (lam / 16 / R.coupling) / 2) := by
  classical
  have hx1 : 1 ≤ R.coupling := by linarith
  have hx : 0 < R.coupling := by linarith
  have hρ := hρ0.le
  have hL : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  set u := s.cutGaussianMixPotential lam τ X with hu
  set d : FreeCoords s.free → ℝ := fun η => s.cutoffProduct η * Real.exp (-(u η)) with hd
  obtain ⟨U₁, hU₁o, hU₁b, hU₁s⟩ := hmix.contDiffOn_nhds
  obtain ⟨U₂, hU₂o, hU₂b, hU₂s⟩ := hcr.contDiffOn
  obtain ⟨U₃, hU₃o, hU₃b, hU₃s⟩ := hpart.contDiffOn_nhds
  have hcs : ContDiffOn ℝ 3 s.totalCost U₂ := hU₂s
  have hd0 : ∀ η, 0 ≤ d η := fun η => mul_nonneg (cutoffProduct_nonneg s η) (Real.exp_pos _).le
  have hI : ∀ f : FreeCoords s.free → ℝ, Continuous f → Integrable fun η => f η * d η := fun f hf =>
    integrable_mul_law s hρ0 hp hrim hU₁b hU₁s.continuousOn hf
  have hId : Integrable d := by simpa using hI (fun _ => 1) continuous_const
  have hpos : 0 < ∫ η, d η := integral_cutoff_law_pos s hρ0 hId
  obtain ⟨M, hMb, hMC, hMrows⟩ := hcr.decay
  have hz := inBalls_zero s hρ
  have hM0 : ∀ b b', 0 ≤ M b b' := by
    intro b b'
    have hu1 : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ = 1 := by simp
    exact (abs_nonneg _).trans (hMb 0 hz b b' _ _ hu1 hu1)
  have hM : ∀ ξ, s.InBalls ξ → ∀ (b b' : s.free) (Z Z' : EuclideanSpace ℝ (Fin 3)), ‖Z‖ = 1 → ‖Z'‖ = 1 →
      |fderiv ℝ (fderiv ℝ s.totalCost) ξ (Pi.single b Z : TangentField s.free)
        (Pi.single b' Z' : TangentField s.free)| ≤ M b b' := by
    intro ξ hξ b b' Z Z' hZ hZ'
    have h1 := hMb ξ hξ b b' Z Z' hZ hZ'
    unfold StepSettings.mixedSecondDeriv at h1
    rwa [show s.costSum = s.totalCost from rfl,
      deriv_deriv_update_eq hU₂o (hcs.of_le (by norm_num)) (hU₂b ξ hξ)] at h1
  have hlineC : ∀ (b : s.free) (Z : EuclideanSpace ℝ (Fin 3)),
      deriv (fun t : ℝ => s.totalCost (Function.update 0 b (t • Z))) 0 =
        fderiv ℝ s.totalCost 0 (Pi.single b Z : TangentField s.free) := by
    intro b Z
    simp only [update_zero_smul_eq]
    exact deriv_line_eq_fderiv ((hcs.contDiffAt (hU₂o.mem_nhds (hU₂b 0 hz))).differentiableAt (by norm_num))
  have hA : ∀ b ∈ s.freeBondsOf Y, ∀ Z : EuclideanSpace ℝ (Fin 3),
      R.coupling * |fderiv ℝ s.totalCost 0 (Pi.single b Z : TangentField s.free)| ≤ C3 * ‖Z‖ := by
    intro b hb Z
    by_cases hZ : Z = 0
    · simp [hZ]
    have hZn : ‖Z‖ ≠ 0 := norm_ne_zero_iff.mpr hZ
    have hblk : bondBlock (R := R) b.1 = Y := by simpa [ChartSetting.freeBondsOf] using hb
    have h1 := hS3 b (‖Z‖⁻¹ • Z) (norm_smul_inv_norm hZ) (by
      rw [hblk, supDist_self]
      simp)
    rw [hlineC] at h1
    have e1 : (Pi.single b Z : TangentField s.free) = ‖Z‖ • (Pi.single b (‖Z‖⁻¹ • Z) : TangentField s.free) := by
      rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hZn, one_smul]
    rw [e1, map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (norm_nonneg Z)]
    nlinarith [norm_nonneg Z]
  set Near : Finset s.free := Finset.univ.filter fun b =>
    (16 * R.params.side : ℝ) * supDist (bondBlock (R := R) b.1) Y ≤ R.range with hNear
  set Nr : Finset s.free := Finset.univ.filter fun b =>
    (32 * R.params.side : ℝ) * supDist (bondBlock (R := R) b.1) Y ≤ R.range with hNr
  have hslope : ∀ b Z, ‖Z‖ = 1 → |partialSlope u 0 b Z| ≤ if b ∈ Near then C3 + CJ else Cu * R.coupling := by
    intro b Z hZ
    split_ifs with hb
    · have hb' : (16 * R.params.side : ℝ) * supDist (bondBlock (R := R) b.1) Y ≤ R.range :=
        (Finset.mem_filter.mp hb).2
      have hU : IsOpen (U₂ ∩ U₃) := hU₂o.inter hU₃o
      have h0 : (0 : FreeCoords s.free) ∈ U₂ ∩ U₃ := ⟨hU₂b 0 hz, hU₃b 0 hz⟩
      have hsp := deriv_partPotential_line s (b := b) (Z := Z) hU h0 (hcs.mono Set.inter_subset_left)
        (hU₃s.mono Set.inter_subset_right)
      have hdu : DifferentiableAt ℝ (s.partPotential 0) 0 :=
        (hU₃s.contDiffAt (hU₃o.mem_nhds (hU₃b 0 hz))).differentiableAt (by norm_num)
      have hline : HasDerivAt (fun t : ℝ => (0 : FreeCoords s.free) + t • (Pi.single b Z : TangentField s.free))
          (Pi.single b Z : TangentField s.free) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single b Z : TangentField s.free)).const_add
          (0 : FreeCoords s.free)
      have hdf : DifferentiableAt ℝ (fun t : ℝ => s.partPotential 0 (Function.update 0 b (t • Z))) 0 := by
        simp only [update_zero_smul_eq]
        exact (HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdu.hasFDerivAt hline (by simp)).differentiableAt
      have h3 := hS3 b Z hZ hb'
      have h4 := hSJ b Z hZ
      refine abs_partialSlope_mix_le s hτ0 hτ1 X hZ (by positivity) hdf ?_
      rw [hsp]
      have h5 : |R.coupling * deriv (fun t : ℝ => s.totalCost (Function.update 0 b (t • Z))) 0| ≤ C3 := by
        rwa [abs_mul, abs_of_pos hx]
      exact (abs_sub _ _).trans (add_le_add h5 h4)
    · have h1 := hmix.firstDeriv_le 0 hz b Z hZ
      exact h1
  have hmoment : ∀ b ∈ Nr, weightedMean d (fun η => ‖η b‖ ^ 2) ≤
      (CF + CF * (C3 + CJ) ^ 2 * W + CF * Cu ^ 2) / R.coupling := by
    intro b hb
    have hb' : (32 * R.params.side : ℝ) * supDist (bondBlock (R := R) b.1) Y ≤ R.range :=
      (Finset.mem_filter.mp hb).2
    have h1 := hfact (fun b' => if b' ∈ Near then C3 + CJ else Cu * R.coupling) hslope b
    refine moment_le_of_slopes s (e := fun b' => Real.exp (-(2 * R.params.rt * s.bondDist b b'))) hx1 hCF
      (fun _ => (Real.exp_pos _).le) ?_ ?_ hq1 h1
    · have := hW b
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun b' _ => ?_)) this
      unfold ChartSetting.bondDist bondBlockDist
      rw [supDist_comm]
    · set D := R.range / (32 * R.params.side) with hD
      have h2 := sum_exp_far_bonds_le s hBd (hAs) (bondBlock (R := R) b.1) D hBd0
      refine le_trans ?_ h2
      have hsub : Finset.univ \ Near ⊆ (Finset.univ : Finset s.free).filter
          (fun b' => D ≤ supDist (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1)) := by
        intro b' hb''
        have hn : b' ∉ Near := (Finset.mem_sdiff.mp hb'').2
        have hn' : ¬ (16 * R.params.side : ℝ) * supDist (bondBlock (R := R) b'.1) Y ≤ R.range := fun h =>
          hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, div_le_supDist_of_far s hL hb' hn'⟩
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun b' _ => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le)
      unfold ChartSetting.bondDist bondBlockDist
      rw [supDist_comm]
  have hmom : ∀ b, weightedMean d (fun η => ‖η b‖ ^ 2) ≤ 1 := by
    intro b
    have h1 := abs_weightedMean_le (G := fun η => ‖η b‖ ^ 2) (B := fun _ => 1) hd0 (hI _ continuous_const)
      (fun η hη => ?_) hpos
    · rw [weightedMean_const hpos] at h1
      exact (le_abs_self _).trans h1
    · have hc : s.cutoffProduct η ≠ 0 := fun h0 => hη (by
        show s.cutoffProduct η * _ = 0
        rw [h0, zero_mul])
      have h2 := coordNorm_lt_of_cutoffProduct_ne_zero s hc b
      rw [coordNorm_eq_norm] at h2
      have h3 : ‖η b‖ ≤ 1 := by linarith
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (norm_nonneg _) h3
  have hFY : freeBondsAt s.free Y ⊆ Nr := by
    intro b hb
    have hblk : bondBlock (R := R) b.1 = Y := by simpa [freeBondsAt] using hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hblk, supDist_self]
    simp
  have hpoint : ∀ η, d η ≠ 0 → |(s.restrictedSplit lam X).interaction Y η - gaussianPart lam Y η| ≤ 2 * J +
      (∑ b ∈ freeBondsAt s.free Y, (C3 * ‖η b‖ + R.coupling * ((∑ b', M b b' * ‖η b'‖) * ‖η b‖))) +
      R.coupling * lam / 2 * ∑ b ∈ freeBondsAt s.free Y, ‖η b‖ ^ 2 := by
    intro η hη
    have hc : s.cutoffProduct η ≠ 0 := fun h0 => hη (by
      show s.cutoffProduct η * _ = 0
      rw [h0, zero_mul])
    exact abs_interaction_sub_gaussianPart_le s lam hlam.le X hU₂o hU₂b hcs hρ hx hX hM0 hM hJ hA
      fun b => (coordNorm_lt_of_cutoffProduct_ne_zero s hc b).le
  have hcore := abs_weightedMean_le_of_quadratic hd0 hpos hI
    (G := fun η => (s.restrictedSplit lam X).interaction Y η - gaussianPart lam Y η)
    (x := R.coupling) (lam := lam) (J := J) (A₀ := C3) (m₀ := CF + CF * (C3 + CJ) ^ 2 * W + CF * Cu ^ 2)
    (P := Ch * Bd + lam / 16 / (2 * R.params.rt)) (Fr := lam / 16 / R.coupling) (Bd := Bd) hx1 hlam.le hC3
    (by
      positivity)
    (by positivity) (FY := freeBondsAt s.free Y) (Nr := Nr) (M := M) hM0 hpoint hmom hmoment hFY
    (fun b _ => sum_row_le s hrt hM0 (fun b b' => hMC b b') hCh hMrows hBd b)
    (fun b hb => by
      have hblk : bondBlock (R := R) b.1 = Y := by simpa [freeBondsAt] using hb
      refine sum_row_far_le s hrt hM0 hx hlam.le hMrows (D := R.range / (32 * R.params.side))
        (fun b' hb' => ?_) hq2
      have hn : b' ∉ Nr := (Finset.mem_sdiff.mp hb').2
      have hn' : ¬ (32 * R.params.side : ℝ) * supDist (bondBlock (R := R) b'.1) Y ≤ R.range := fun h =>
        hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have := div_le_supDist_of_not_le s hn'
      unfold bondBlockDist
      rw [hblk, supDist_comm]
      exact this)
    (by positivity) (hBd Y)
  have hlaw : (s.restrictedSplit lam X).interpolatedDensity lam τ =
      fun η => Real.exp (τ * s.partPotential 0 0) * d η := by
    funext η
    exact restrictedSplit_interpolatedDensity s lam τ X hU₂o hU₂b hcs hρ (inBalls_restrictTo s hρ X)
      (fun η h v hv => inBalls_smul s hρ η h v hv) η
  rw [hlaw, weightedMean_const_mul_density (Real.exp_pos _)]
  exact hcore
end Estimates
section Arithmetic
theorem mul_mul_exp_le_one {x c g Cf : ℝ} (hx : 1 ≤ x) (hCf : 1 ≤ Cf)
    (hy7 : Cf * x ^ Cf * Real.exp (-(c * g)) ≤ Real.exp (-(x ^ (1 / 200 : ℝ)))) :
    Cf * (x * Real.exp (-(c * g))) ≤ 1 := by
  have hxpos : 0 < x := by linarith
  have hE1 : Real.exp (-(x ^ (1 / 200 : ℝ))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have := Real.rpow_nonneg hxpos.le (1 / 200 : ℝ)
    linarith
  have h1 : x ≤ x ^ Cf := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ x ^ Cf := Real.rpow_le_rpow_of_exponent_le hx hCf
  have h2 := Real.exp_pos (-(c * g))
  have h3 : x * Real.exp (-(c * g)) ≤ x ^ Cf * Real.exp (-(c * g)) := mul_le_mul_of_nonneg_right h1 h2.le
  have h4 : Cf * (x * Real.exp (-(c * g))) ≤ Cf * (x ^ Cf * Real.exp (-(c * g))) :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  calc Cf * (x * Real.exp (-(c * g))) ≤ Cf * (x ^ Cf * Real.exp (-(c * g))) := h4
    _ = Cf * x ^ Cf * Real.exp (-(c * g)) := by ring
    _ ≤ 1 := hy7.trans hE1
theorem exp_neg_mul_le {rt D cg a : ℝ} (hrt : 0 < rt) (hcg : cg = rt * a) (hD : a - 1 ≤ D) :
    Real.exp (-(rt * D)) ≤ Real.exp rt * Real.exp (-cg) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  rw [hcg]
  nlinarith
theorem mul_mul_le_one_of_le {x K q e E : ℝ} (hx : 0 < x) (hK : 0 ≤ K) (hE : 0 < E) (he : 0 ≤ e)
    (hq : q ≤ E * e) (hc : (1 + (K + 2) * E) * (x * e) ≤ 1) : (K + 2) * (x * q) ≤ 1 := by
  have h1 : x * q ≤ E * (x * e) := by
    have := mul_le_mul_of_nonneg_left hq hx.le
    linarith [mul_comm x (E * e), mul_assoc E e x, mul_comm e x, mul_assoc x E e, mul_left_comm x E e]
  have h2 : (K + 2) * (x * q) ≤ (K + 2) * (E * (x * e)) := mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3 : 0 ≤ x * e := by positivity
  nlinarith
theorem le_exp_mul_exp_sub_one {x K q a : ℝ} (hx : 2 ≤ x) (hK : 0 ≤ K) (hq : q = Real.exp (-a))
    (h : (K + 2) * (x * q) ≤ 1) : x ≤ Real.exp a * Real.exp a - 1 := by
  have hEp : 0 < Real.exp a := Real.exp_pos _
  have hqp : 0 < q := by rw [hq]; exact Real.exp_pos _
  have h1 : 2 * (x * q) ≤ 1 := by
    have : 0 ≤ K * (x * q) := by positivity
    nlinarith
  have h3 : q * Real.exp a = 1 := by
    rw [hq, ← Real.exp_add]
    simp
  have h2 : 2 * x ≤ Real.exp a := by
    have h4 := mul_le_mul_of_nonneg_right h1 hEp.le
    have h5 : 2 * (x * q) * Real.exp a = 2 * x * (q * Real.exp a) := by ring
    rw [h5, h3] at h4
    linarith
  nlinarith
theorem mul_mul_mul_le_one {x K q Bd As : ℝ} (hBd : Bd * As = K) (hx : 0 ≤ x) (hq : 0 ≤ q) (hK : 0 ≤ K)
    (h : (K + 2) * (x * q) ≤ 1) : x * (Bd * (As * q)) ≤ 1 := by
  have h1 : x * (Bd * (As * q)) = K * (x * q) := by
    rw [← hBd]
    ring
  rw [h1]
  have : 0 ≤ x * q := by positivity
  nlinarith
theorem le_one_of_two_mul_add_le {N σ ρ ρA : ℝ} (h : 2 * N * σ + 2 * ρ ≤ ρA) (hρA : ρA ≤ 1) (hN : 0 < N)
    (hσ : 0 < σ) : ρ ≤ 1 := by
  nlinarith [mul_pos hN hσ]
theorem two_mul_add_le_mul {Cj Lg K : ℝ} (hL : 1 ≤ Lg) (hK : 0 ≤ K) : 2 * (Cj * Lg) + K ≤ (2 * Cj + K + 1) * Lg := by
  nlinarith
theorem mul_div_div_two {x a : ℝ} (hx : 0 < x) : x * (a / x) / 2 = a / 2 := by
  field_simp
end Arithmetic
end GainMean
open GainMean in
set_option maxHeartbeats 2000000 in
theorem gainMeanLogBound_of_estimates (hConv : SettingsUniformlyConvex) (hCost : CostHessianFloor)
    (hFacts : ConvexLawEstimates) (hSum : FreeBondWeightsSummable)
    (hBlocks : BondsPerBlockBound) (hSlope : FrameSlopeBound)
    (hSlopeJ : LogJacobianSlopeBound) (hLog : LogJacobianBound)
    (hFloors : EventuallyFloorConditions) (hRim : CutoffFactorIsRadialCutoff) : GainMeanLogBound := by
  obtain ⟨rt₁, hrt₁, hC⟩ := hConv
  obtain ⟨rt₂, hrt₂, hH⟩ := hCost
  refine ⟨fun c => min (rt₁ c) (rt₂ c), fun c => lt_min (hrt₁ c) (hrt₂ c), fun T hT hrt => ?_⟩
  obtain ⟨Cc, yc, hCc, hCT⟩ := hC T hT (hrt.trans (min_le_left _ _))
  obtain ⟨Ch, yh, hCh, hHT⟩ := hH T hT (hrt.trans (min_le_right _ _))
  obtain ⟨C3, y3, hC3, hS3⟩ := hSlope T hT
  obtain ⟨CJ, yJ, hCJ, hSJ⟩ := hSlopeJ T hT
  obtain ⟨Cj, yj, hCj, hLg⟩ := hLog T hT
  have hrtT : 0 < T.rt := hT.rt_pos
  have hσT : 0 < T.threshold := hT.σ_pos
  obtain ⟨_, _, hlam, hρA0, hρA1, _⟩ := hT.chain
  have hρT : 0 < T.ballRadius := by
    unfold ParameterAssignment.ballRadius
    positivity
  have hLpos : (0 : ℝ) < T.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T.side)
  obtain ⟨CF, hCF, hFa⟩ := hFacts (T.stepParameters 0) T.lam Cc hσT hrtT hlam hCc.le
  obtain ⟨As, hAs0, hAs⟩ := exists_sum_exp_supDist_le (2 * T.rt) (by positivity)
  set Bd : ℝ := (T.stepParameters 0).blockBondBound with hBdd
  set W : ℝ := (T.stepParameters 0).bondWeightBound with hWd
  have hBd0 : 0 ≤ Bd := by
    show (0 : ℝ) ≤ 4 * (2 * (T.side : ℝ)) ^ 4
    positivity
  have hW0 : 0 ≤ W := by
    show (0 : ℝ) ≤ Bd * _
    refine mul_nonneg hBd0 (pow_nonneg (tsum_nonneg fun k => (Real.exp_pos _).le) 4)
  set c₂ : ℝ := T.rt / (32 * T.side) with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  set Cf : ℝ := 1 + (Bd * As + 2) * Real.exp T.rt with hCfd
  have hCf1 : 1 ≤ Cf := by
    have : 0 ≤ (Bd * As + 2) * Real.exp T.rt := by positivity
    linarith
  obtain ⟨yf, hF⟩ := hFloors T hT Cf c₂ (by linarith) hc₂0
  set m₀ : ℝ := CF + CF * (C3 + CJ) ^ 2 * W + CF * Cc ^ 2 with hm₀
  set Q : ℝ := C3 ^ 2 / 2 + ((1 + T.lam) / 2 + (Ch * Bd + T.lam / 16 / (2 * T.rt))) * m₀ + T.lam / 16 / 2
    with hQ
  have hm₀0 : 0 ≤ m₀ := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨2 * Cj + Bd * Q + 1, max (max (max yc yh) (max y3 yJ)) (max (max yj yf) (max (Real.exp 1) 2)),
    by positivity, fun y hy R hR n _ hn s hs c Y hst hmk hoff X hX τ hτ0 hτ1 => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨⟨⟨hyc, hyh⟩, hy3, hyJ⟩, ⟨hyj, hyf⟩, hye, hy2⟩ := hy
  have hx : y ≤ R.coupling := hR.le_coupling
  have hxe : Real.exp 1 ≤ R.coupling := hye.trans hx
  have hx2 : 2 ≤ R.coupling := hy2.trans hx
  have hxpos : 0 < R.coupling := by linarith
  have hlog1 : 1 ≤ Real.log R.coupling := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hrte : R.params.rt = T.rt := by rw [hR.params_eq]; rfl
  have hσe : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hρe : R.ballRadius = T.ballRadius := by
    show R.params.threshold / 64 = T.threshold / 64
    rw [hσe]
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    rw [hρe, hR.barrierFn_eq]
    exact hT.cut
  have hρ1 : R.ballRadius ≤ 1 := by
    rw [hρe]
    obtain ⟨_, _, _, _, _, _, _, hNp, _⟩ := hT.chain
    exact le_one_of_two_mul_add_le hT.ρ_le hρA1 (hNp 0) hσT
  have hρ0 : 0 < R.ballRadius := by rw [hρe]; exact hρT
  have hRl : R.params = { T.stepParameters 0 with y₁ := y } := hR.params_eq
  have hconv := hCT y hyc R hR n hn s hs
  have hcr := hHT y hyh R hR n hn s hs
  obtain ⟨_, hpart, _, _, hmix⟩ := hconv
  have hfa := hFa y R hRl hcut hxpos n s (s.cutGaussianMixPotential T.lam τ X) (hmix τ X hτ0 hτ1)
  have hBdR : ∀ Z : TorusSite n,
      (((Finset.univ : Finset s.free).filter fun b => bondBlock (R := R) b.1 = Z).card : ℝ) ≤ Bd := by
    intro Z
    have h1 := card_bondBlock_le s hBlocks Z
    have h2 : R.params.blockBondBound = Bd := by
      show 4 * (2 * (R.params.side : ℝ)) ^ 4 = 4 * (2 * (T.side : ℝ)) ^ 4
      rw [hLe]
    rwa [h2] at h1
  have hWR : ∀ b₀ : s.free, ∑ b, Real.exp (-(2 * R.params.rt * s.bondDist b b₀)) ≤ W := by
    intro b₀
    have h1 := hSum R (by rw [hrte]; exact hrtT) n s b₀
    have h2 : R.params.bondWeightBound = W := by
      rw [hR.params_eq]
      rfl
    rwa [h2] at h1
  have hJ : ∀ ξ, s.InBalls ξ → |s.logJacobianAt Y ξ| ≤ Cj * Real.log R.coupling := fun ξ hξ =>
    hLg y R hR.params_eq hR.anchorRadius_eq (hyj.trans hx) n s Y ξ hξ
  set D : ℕ := R.range / (32 * R.params.side) with hD
  have hDge : (R.range : ℝ) / (32 * T.side) - 1 ≤ (D : ℝ) := by
    have h1 : R.range < (32 * R.params.side) * (D + 1) := by
      have := Nat.lt_mul_div_succ R.range
        (Nat.mul_pos (by norm_num : 0 < 32) (Nat.pos_of_ne_zero (NeZero.ne R.params.side)))
      simpa [hD] using this
    have h2 : (R.range : ℝ) < (32 * T.side) * ((D : ℝ) + 1) := by
      have h3 : ((R.range : ℕ) : ℝ) < ((32 * R.params.side * (D + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      rw [hLe] at h3
      push_cast at h3
      exact h3
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    linarith
  have hxc : (1 + (Bd * As + 2) * Real.exp T.rt) *
      (R.coupling * Real.exp (-(c₂ * (clusterRange R.coupling : ℝ)))) ≤ 1 :=
    mul_mul_exp_le_one (by linarith) hCf1 (hF R.coupling (hyf.trans hx)).stretched_tail.1
  have hqE : Real.exp (-(T.rt * (D : ℝ))) ≤
      Real.exp T.rt * Real.exp (-(c₂ * (clusterRange R.coupling : ℝ))) := by
    refine exp_neg_mul_le hrtT ?_ hDge
    have hr : (R.range : ℝ) = (clusterRange R.coupling : ℝ) := rfl
    rw [hc₂, hr]
    field_simp
  have hK0 : 0 ≤ Bd * As := mul_nonneg hBd0 hAs0
  have hxq : (Bd * As + 2) * (R.coupling * Real.exp (-(T.rt * (D : ℝ)))) ≤ 1 :=
    mul_mul_le_one_of_le hxpos hK0 (Real.exp_pos _) (Real.exp_pos _).le hqE hxc
  have hq1 : R.coupling * (Bd * (As * Real.exp (-(2 * R.params.rt *
      ((R.range / (32 * R.params.side) : ℕ) : ℝ) / 2)))) ≤ 1 := by
    have e : -(2 * R.params.rt * ((R.range / (32 * R.params.side) : ℕ) : ℝ) / 2) = -(T.rt * (D : ℝ)) := by
      rw [hrte]
      ring
    rw [e]
    exact mul_mul_mul_le_one rfl hxpos.le (Real.exp_pos _).le hK0 hxq
  have hq2 : R.coupling ≤ Real.exp (2 * R.params.rt * ((R.range / (32 * R.params.side) : ℕ) : ℝ)) - 1 := by
    have e : 2 * R.params.rt * ((R.range / (32 * R.params.side) : ℕ) : ℝ) = T.rt * (D : ℝ) + T.rt * (D : ℝ) := by
      rw [hrte]
      ring
    rw [e, Real.exp_add]
    exact le_exp_mul_exp_sub_one hx2 hK0 rfl hxq
  have hAsR : ∀ (y' : TorusSite n) (D' : ℕ),
      ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D' ≤ supDist Y y'),
        Real.exp (-(2 * R.params.rt * supDist Y y')) ≤ As * Real.exp (-(2 * R.params.rt * D' / 2)) := by
    intro y' D'
    rw [hrte]
    exact hAs n y' D'
  have hmain := abs_weightedMean_gain_le s hlam hτ0 hτ1 X hX hρ0 hρ1 hcut hRim hx2 (by rw [hrte]; exact hrtT)
    (Cu := Cc) (Ch := Ch) (C3 := C3) (CJ := CJ) (J := Cj * Real.log R.coupling) (CF := CF) (W := W) (Bd := Bd)
    (As := As)
    hCc.le hCh.le hC3.le hCJ.le hCF.le hBd0 hW0 hcr (hpart 0 le_rfl zero_le_one) (hmix τ X hτ0 hτ1) hfa.2.1 hWR
    hBdR hAsR
    (fun b Z hZ hb => hS3 y hy3 R hR n hn s hs c Y hst hmk hoff b Z hZ hb)
    (fun b Z hZ => hSJ y hyJ R hR n hn s hs b Z hZ) hJ hq1 hq2
  refine hmain.trans ?_
  rw [hrte]
  rw [mul_div_div_two hxpos]
  exact two_mul_add_le_mul hlog1 (mul_nonneg hBd0 hQ0)
end YangMills.Construction.ClusterExpansionOfAStep
end
