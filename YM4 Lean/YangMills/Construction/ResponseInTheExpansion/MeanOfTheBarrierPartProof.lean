import YangMills.Construction.ResponseInTheExpansion.MeanOfASlotOfOrderTwoProof
import YangMills.Construction.ResponseInTheExpansion.MeanOfTheBarrierPart
import YangMills.Construction.ResponseInTheExpansion.SizeOfASumOfObservables
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOverASecondMeasure
import YangMills.Construction.SummableBoundsOfTheFlow.PowersOfACut
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Cumulants ConvexObservables TiltedMeans Estimates
  WeightedResponses
namespace ResponseInTheExpansion
namespace CutoffTermMean
variable {F : BlockFrame}
section Radial
variable {ρ : ℝ} {p : ℝ → ℝ}
def radialTerm (p : ℝ → ℝ) (v : BondVector) : ℝ := ‖v‖ * deriv p ‖v‖
theorem deriv_cutoff_eq_zero_of_lt (hPow : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ}
    (h0 : 0 < u) (h1 : u < 5 * ρ / 8) :
    deriv p u = 0 := by
  have := (hPow ρ p hρ hp).2.1 u h0 h1 1 le_rfl
  simpa [iteratedDeriv_one] using this
theorem radialTerm_eq_zero_of_lt (hPow : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector}
    (h1 : ‖v‖ < 5 * ρ / 8) :
    radialTerm p v = 0 := by
  unfold radialTerm
  by_cases h0 : v = 0
  · simp [h0]
  · rw [deriv_cutoff_eq_zero_of_lt hPow hρ hp (norm_pos_iff.2 h0) h1, mul_zero]
theorem radialTerm_eventually_zero (hPow : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector}
    (h1 : ‖v‖ < 5 * ρ / 8) :
    radialTerm p =ᶠ[𝓝 v] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h1] with w hw using
    radialTerm_eq_zero_of_lt hPow hρ hp hw
theorem contDiffAt_deriv_cutoff (_hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    ContDiffAt ℝ 1 (deriv p) u := by
  have hs : Set.Ico 0 ρ ∈ 𝓝 u := Ico_mem_nhds h0 h1
  have h2 : ContDiffAt ℝ 2 p u := by simpa using contDiffAt_infty.1 (hp.smooth.contDiffAt hs) 2
  have h3 := (h2.fderiv_right (m := 1) (by norm_num)).clm_apply (contDiffAt_const (c := (1 : ℝ)))
  have e : (fun x => (fderiv ℝ p x) 1) = deriv p := by
    funext y
    simp
  rwa [e] at h3
theorem contDiffAt_radialTerm (hPow : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector}
    (hv : ‖v‖ < ρ) :
    ContDiffAt ℝ 1 (radialTerm p) v := by
  by_cases h1 : ‖v‖ < 5 * ρ / 8
  · exact contDiffAt_const.congr_of_eventuallyEq (radialTerm_eventually_zero hPow hρ hp h1)
  · have hpos : 0 < ‖v‖ := by
      have : 0 < 5 * ρ / 8 := by positivity
      linarith
    have hv0 : v ≠ 0 := norm_pos_iff.1 hpos
    have hn : ContDiffAt ℝ 1 (fun w : BondVector => ‖w‖) v := contDiffAt_norm ℝ hv0
    have hd := contDiffAt_deriv_cutoff hρ hp hpos hv
    exact hn.mul (ContDiffAt.comp (g := deriv p) (f := fun w : BondVector => ‖w‖) v hd hn)
theorem norm_fderiv_radialTerm_le (hPow : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector}
    (hv : ‖v‖ < ρ) :
    ‖fderiv ℝ (radialTerm p) v‖ ≤ |deriv p ‖v‖| + ρ * |deriv (deriv p) ‖v‖| := by
  by_cases h1 : ‖v‖ < 5 * ρ / 8
  · rw [(radialTerm_eventually_zero hPow hρ hp h1).fderiv_eq]
    simp only [fderiv_fun_const, Pi.zero_apply, norm_zero]
    positivity
  · have hpos : 0 < ‖v‖ := by
      have : 0 < 5 * ρ / 8 := by positivity
      linarith
    have hv0 : v ≠ 0 := norm_pos_iff.1 hpos
    have hn1 : ContDiffAt ℝ 1 (fun w : BondVector => ‖w‖) v := contDiffAt_norm ℝ hv0
    have hn : DifferentiableAt ℝ (fun w : BondVector => ‖w‖) v := hn1.differentiableAt (by norm_num)
    have hd : HasDerivAt (deriv p) (deriv (deriv p) ‖v‖) ‖v‖ :=
      ((contDiffAt_deriv_cutoff hρ hp hpos hv).differentiableAt (by norm_num)).hasDerivAt
    have hg : HasDerivAt (fun u => u * deriv p u) (1 * deriv p ‖v‖ + ‖v‖ * deriv (deriv p) ‖v‖) ‖v‖ :=
      (hasDerivAt_id ‖v‖).mul hd
    have hc := hg.comp_hasFDerivAt v hn.hasFDerivAt
    have e : radialTerm p = (fun u => u * deriv p u) ∘ fun w : BondVector => ‖w‖ := rfl
    rw [e, hc.fderiv, norm_smul]
    have hnorm : ‖fderiv ℝ (fun w : BondVector => ‖w‖) v‖ ≤ 1 := by
      have := norm_fderiv_le_of_lipschitz ℝ (x₀ := v) (lipschitzWith_one_norm (E := BondVector))
      simpa using this
    have h2 : ‖1 * deriv p ‖v‖ + ‖v‖ * deriv (deriv p) ‖v‖‖ ≤ |deriv p ‖v‖| + ρ * |deriv (deriv p) ‖v‖| := by
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [one_mul, abs_mul, abs_of_nonneg (norm_nonneg v)]
      have := mul_le_mul_of_nonneg_right hv.le (abs_nonneg (deriv (deriv p) ‖v‖))
      linarith
    calc _ ≤ ‖1 * deriv p ‖v‖ + ‖v‖ * deriv (deriv p) ‖v‖‖ * 1 :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ ≤ _ := by simpa using h2
end Radial
section Sizes
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem momentBound_of_le (hLaw : normalizedBallLawIsProbabilityStatement) {ρ : ℝ} {p : ℝ → ℝ}
    {Ψ H g : BondField ι → ℝ} {q : ℕ}
    {B : ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) (hc : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ})
    (hgI : Integrable (fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η))
    (hle : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H η| ^ q ≤ g η)
    (hB : ballExpectation (cutoffFactor ρ p) Ψ g ≤ B ^ q) : MomentBound (cutoffFactor ρ p) Ψ H q B := by
  obtain ⟨hprob, hmean, hint, hball, -⟩ := hLaw ι ρ p Ψ hρ hp hΨ
  have hUo : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    have : {η : BondField ι | ∀ b, ‖η b‖ < ρ} = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt ((continuous_apply b).norm) continuous_const
  have hrestr := Measure.restrict_eq_self_of_ae_mem hball
  have hHm : AEStronglyMeasurable H (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
    rw [← hrestr]
    exact hc.aestronglyMeasurable hUo.measurableSet
  have hgP := (hint g).2 hgI
  have hHq : Integrable (fun η => |H η| ^ q) (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
    refine Integrable.mono' hgP ((hHm.norm.pow q).congr ?_) ?_
    · exact Filter.Eventually.of_forall fun η => by simp
    · filter_upwards [hball] with η hη
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle η hη
  refine ⟨(hint _).mp hHq, ?_⟩
  rw [← hmean]
  refine (integral_mono_ae hHq hgP ?_).trans ?_
  · filter_upwards [hball] with η hη using hle η hη
  · rwa [hmean]
omit [DecidableEq ι] in
theorem ballExpectation_const_mul (r : ℝ → ℝ) (Ψ f : BondField ι → ℝ) (a : ℝ) :
    ballExpectation r Ψ (fun η => a * f η) = a * ballExpectation r Ψ f := by
  unfold ballExpectation
  have e : (fun η => a * f η * ballDensity r Ψ η) = fun η => a * (f η * ballDensity r Ψ η) := by
    funext η
    ring
  rw [e, integral_const_mul, mul_div_assoc]
def radialSizeConstant (ρ : ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (q : ℕ) : ℝ :=
  ρ * (1 + |Cr 1 q q|) + 2 * (1 + ρ) * (1 + |Cr 1 q 0| + |Cr 2 q 0|) + 1
theorem radialSizeConstant_pos {ρ : ℝ} (hρ : 0 < ρ) (Cr : ℕ → ℕ → ℕ → ℝ) (q : ℕ) : 0 < radialSizeConstant ρ Cr q := by
  unfold radialSizeConstant
  positivity
private theorem pow_value_le {ρ C y : ℝ} {q : ℕ} {B : ℝ} (hρ : 0 < ρ) (hy : 0 ≤ y) (hB : ρ * (1 + |C|) ≤ B)
    (hq : 1 ≤ q) :
    ρ ^ q * (|C| * y ^ q) ≤ (B * y) ^ q := by
  have h1 : |C| ≤ (1 + |C|) ^ q := by
    have h2 : 1 + |C| ≤ (1 + |C|) ^ q := le_self_pow₀ (by linarith [abs_nonneg C]) (by omega)
    linarith
  have h3 : (ρ * (1 + |C|)) ^ q ≤ B ^ q := pow_le_pow_left₀ (by positivity) hB q
  rw [mul_pow] at h3
  rw [mul_pow]
  calc ρ ^ q * (|C| * y ^ q) = (ρ ^ q * |C|) * y ^ q := by ring
    _ ≤ (ρ ^ q * (1 + |C|) ^ q) * y ^ q := by gcongr
    _ ≤ B ^ q * y ^ q := by gcongr
private theorem pow_slope_le {ρ C₁ C₂ B : ℝ} {q : ℕ} (hρ : 0 < ρ) (hB : 2 * (1 + ρ) * (1 + |C₁| + |C₂|) ≤ B)
    (hq : 1 ≤ q) :
    2 ^ (q - 1) * (|C₁| + ρ ^ q * |C₂|) ≤ B ^ q := by
  have hs1 : 1 ≤ 1 + |C₁| + |C₂| := by linarith [abs_nonneg C₁, abs_nonneg C₂]
  have h1 : (2 * (1 + ρ) * (1 + |C₁| + |C₂|)) ^ q ≤ B ^ q := pow_le_pow_left₀ (by positivity) hB q
  refine le_trans ?_ h1
  rw [mul_pow, mul_pow]
  have h2 : (2 : ℝ) ^ (q - 1) ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : 1 + |C₁| + |C₂| ≤ (1 + |C₁| + |C₂|) ^ q := le_self_pow₀ hs1 (by omega)
  have h4 : (1 : ℝ) ≤ (1 + ρ) ^ q := one_le_pow₀ (by linarith)
  have h5 : ρ ^ q ≤ (1 + ρ) ^ q := pow_le_pow_left₀ hρ.le (by linarith) q
  have h6 : |C₁| + ρ ^ q * |C₂| ≤ (1 + ρ) ^ q * (1 + |C₁| + |C₂|) ^ q := by
    have a1 : |C₁| ≤ (1 + ρ) ^ q * |C₁| := le_mul_of_one_le_left (abs_nonneg _) h4
    have a2 : ρ ^ q * |C₂| ≤ (1 + ρ) ^ q * |C₂| := mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
    have a3 : (1 + ρ) ^ q * (|C₁| + |C₂|) ≤ (1 + ρ) ^ q * (1 + |C₁| + |C₂|) ^ q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    nlinarith
  calc 2 ^ (q - 1) * (|C₁| + ρ ^ q * |C₂|) ≤ 2 ^ q * ((1 + ρ) ^ q * (1 + |C₁| + |C₂|) ^ q) :=
        mul_le_mul h2 h6 (by positivity) (by positivity)
    _ = _ := by ring
theorem radialTerm_hasLocalSize (hLaw : normalizedBallLawIsProbabilityStatement) (hPow : cutoffDerivBoundsStatement)
    {ρ x κ : ℝ} {p : ℝ → ℝ}
    {Ψ : BondField ι → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) (hx : 1 ≤ x)
    (b : ι)
    (hr : ∀ (j q N : ℕ), 1 ≤ j → 1 ≤ q →
      Integrable (fun η : BondField ι => |iteratedDeriv j p ‖η b‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) ∧
      ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) ≤ Cr j q N * (x ^ N)⁻¹)
    (dZ : ι → ℝ) (hdZ : dZ b = 0) :
    ContDiffOn ℝ 1 (fun η : BondField ι => radialTerm p (η b)) {η | ∀ b, ‖η b‖ < ρ} ∧
    HasLocalSize ρ (cutoffFactor ρ p) Ψ (radialSizeConstant ρ Cr) x κ (x ^ (-(1 / 2) : ℝ)) dZ
      (fun η => radialTerm p (η b)) := by
  have hx0 : 0 < x := by linarith
  have hUo : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    have : {η : BondField ι | ∀ b, ‖η b‖ < ρ} = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt ((continuous_apply b).norm) continuous_const
  have hproj : ContDiff ℝ 1 (fun η : BondField ι => η b) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).contDiff
  have hsm : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) →
      ContDiffAt ℝ 1 (fun η : BondField ι => radialTerm p (η b)) η :=
    fun η hη => ContDiffAt.comp (g := radialTerm p) (f := fun η : BondField ι => η b) η
      (contDiffAt_radialTerm hPow hρ hp (hη b)) hproj.contDiffAt
  have hC1 : ContDiffOn ℝ 1 (fun η : BondField ι => radialTerm p (η b)) {η | ∀ b, ‖η b‖ < ρ} :=
    fun η hη => (hsm η hη).contDiffWithinAt
  have hy0 : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hy1 : x ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hysq : (x ^ (-(1 / 2) : ℝ)) ^ 2 = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]
    norm_num
  have hyy : ∀ q : ℕ, (x ^ q)⁻¹ ≤ (x ^ (-(1 / 2) : ℝ)) ^ q := fun q => by
    have h1 : (x ^ q)⁻¹ = ((x ^ (-(1 / 2) : ℝ)) ^ 2) ^ q := by rw [hysq, inv_pow]
    rw [h1, ← pow_mul]
    exact pow_le_pow_of_le_one hy0.le hy1 (by omega)
  have hsx : Real.sqrt x * x ^ (-(1 / 2) : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    norm_num
  have hd1 : iteratedDeriv 1 p = deriv p := iteratedDeriv_one
  have hd2 : iteratedDeriv 2 p = deriv (deriv p) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hpn : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b' : ι,
      bondGradNorm (fun η : BondField ι => radialTerm p (η b)) b' η ≤
        if b' = b then ‖fderiv ℝ (radialTerm p) (η b)‖ else 0 := by
    intro η hη b'
    have hd : HasFDerivAt (radialTerm p) (fderiv ℝ (radialTerm p) (η b)) (η b) :=
      ((contDiffAt_radialTerm hPow hρ hp (hη b)).differentiableAt (by norm_num)).hasFDerivAt
    have hc := HasFDerivAt.comp η hd
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
    have hf : fderiv ℝ (fun η : BondField ι => radialTerm p (η b)) η = _ := hc.fderiv
    unfold bondGradNorm
    rw [hf]
    have h0 : (0 : ℝ) ≤ if b' = b then ‖fderiv ℝ (radialTerm p) (η b)‖ else 0 := by
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    refine ContinuousLinearMap.opNorm_le_bound _ h0 fun e => ?_
    by_cases hb : b' = b
    · subst hb
      simp only [if_true]
      simpa using (fderiv ℝ (radialTerm p) (η b')).le_opNorm e
    · simp [hb]
  have hgc : ∀ b' : ι, ContinuousOn (bondGradNorm (fun η : BondField ι => radialTerm p (η b)) b')
      {η | ∀ b, ‖η b‖ < ρ} := by
    intro b'
    have h1 := hC1.continuousOn_fderiv_of_isOpen hUo le_rfl
    unfold bondGradNorm
    exact (h1.clm_comp continuousOn_const).norm
  refine ⟨hC1, fun η hη => (hsm η hη).differentiableAt (by norm_num), 0, fun q hq => ⟨?_, fun b' => ?_⟩⟩
  · have h1 := hr 1 q q le_rfl hq
    rw [hd1] at h1
    refine momentBound_of_le hLaw hρ hp hΨ (g := fun η => ρ ^ q * |deriv p ‖η b‖| ^ q)
      (hC1.continuousOn.sub continuousOn_const) ?_ ?_ ?_
    · have := h1.1.const_mul (ρ ^ q)
      refine this.congr (Filter.Eventually.of_forall fun η => ?_)
      show _ = _
      ring
    · intro η hη
      rw [sub_zero, ← mul_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ q
      unfold radialTerm
      rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hη b).le (abs_nonneg _)
    · rw [ballExpectation_const_mul]
      have h2 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => |deriv p ‖η b‖| ^ q) ≤
          |Cr 1 q q| * (x ^ (-(1 / 2) : ℝ)) ^ q := by
        refine h1.2.trans ?_
        have h3 : Cr 1 q q ≤ |Cr 1 q q| := le_abs_self _
        have h4 : 0 ≤ (x ^ q)⁻¹ := by positivity
        exact (mul_le_mul_of_nonneg_right h3 h4).trans (mul_le_mul_of_nonneg_left (hyy q) (abs_nonneg _))
      refine (mul_le_mul_of_nonneg_left h2 (by positivity)).trans ?_
      refine pow_value_le hρ hy0.le ?_ hq
      unfold radialSizeConstant
      have : 0 ≤ 2 * (1 + ρ) * (1 + |Cr 1 q 0| + |Cr 2 q 0|) := by positivity
      linarith
  · by_cases hb : b' = b
    · subst hb
      have h1 := hr 1 q 0 le_rfl hq
      have h2 := hr 2 q 0 (by norm_num) hq
      rw [hd1] at h1
      rw [hd2] at h2
      have eB : radialSizeConstant ρ Cr q * Real.sqrt x * x ^ (-(1 / 2) : ℝ) * Real.exp (-(2 * κ * dZ b')) =
          radialSizeConstant ρ Cr q := by
        rw [hdZ, mul_assoc (radialSizeConstant ρ Cr q), hsx]
        simp
      rw [eB]
      refine momentBound_of_le hLaw hρ hp hΨ
        (g := fun η => 2 ^ (q - 1) * (|deriv p ‖η b'‖| ^ q + ρ ^ q * |deriv (deriv p) ‖η b'‖| ^ q)) (hgc b') ?_ ?_ ?_
      · have := ((h1.1.add (h2.1.const_mul (ρ ^ q))).const_mul ((2 : ℝ) ^ (q - 1)))
        refine this.congr (Filter.Eventually.of_forall fun η => ?_)
        show _ = _
        simp only [Pi.add_apply]
        ring
      · intro η hη
        have a1 := hpn η hη b'
        simp only [if_true] at a1
        have a2 := norm_fderiv_radialTerm_le hPow hρ hp (hη b')
        have a0 : 0 ≤ bondGradNorm (fun η : BondField ι => radialTerm p (η b')) b' η := norm_nonneg _
        rw [abs_of_nonneg a0]
        have a3 : bondGradNorm (fun η : BondField ι => radialTerm p (η b')) b' η ^ q ≤
            (|deriv p ‖η b'‖| + ρ * |deriv (deriv p) ‖η b'‖|) ^ q := pow_le_pow_left₀ a0 (a1.trans a2) q
        refine a3.trans ?_
        have := add_pow_le (abs_nonneg (deriv p ‖η b'‖))
          (mul_nonneg hρ.le (abs_nonneg (deriv (deriv p) ‖η b'‖))) q
        rwa [mul_pow] at this
      · have hI1 := (hLaw ι ρ p Ψ hρ hp hΨ).2.2.1
        rw [ballExpectation_const_mul]
        have e : ballExpectation (cutoffFactor ρ p) Ψ
              (fun η => |deriv p ‖η b'‖| ^ q + ρ ^ q * |deriv (deriv p) ‖η b'‖| ^ q) =
            ballExpectation (cutoffFactor ρ p) Ψ (fun η => |deriv p ‖η b'‖| ^ q) +
              ρ ^ q * ballExpectation (cutoffFactor ρ p) Ψ (fun η => |deriv (deriv p) ‖η b'‖| ^ q) := by
          rw [← ballExpectation_const_mul]
          unfold ballExpectation
          rw [← add_div]
          congr 1
          rw [← integral_add h1.1 ?_]
          · refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
            show _ = _
            ring
          · have := h2.1.const_mul (ρ ^ q)
            refine this.congr (Filter.Eventually.of_forall fun η => ?_)
            show _ = _
            ring
        rw [e]
        have b1 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => |deriv p ‖η b'‖| ^ q) ≤ |Cr 1 q 0| := by
          refine h1.2.trans ?_
          simpa using le_abs_self (Cr 1 q 0)
        have b2 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => |deriv (deriv p) ‖η b'‖| ^ q) ≤ |Cr 2 q 0| := by
          refine h2.2.trans ?_
          simpa using le_abs_self (Cr 2 q 0)
        have b3 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => |deriv p ‖η b'‖| ^ q) +
            ρ ^ q * ballExpectation (cutoffFactor ρ p) Ψ (fun η => |deriv (deriv p) ‖η b'‖| ^ q) ≤
            |Cr 1 q 0| + ρ ^ q * |Cr 2 q 0| := add_le_add b1 (mul_le_mul_of_nonneg_left b2 (by positivity))
        refine (mul_le_mul_of_nonneg_left b3 (by positivity)).trans ?_
        refine pow_slope_le hρ ?_ hq
        unfold radialSizeConstant
        have : 0 ≤ ρ * (1 + |Cr 1 q q|) := by positivity
        linarith
    · have hBpos : 0 ≤ radialSizeConstant ρ Cr q * Real.sqrt x * x ^ (-(1 / 2) : ℝ) *
          Real.exp (-(2 * κ * dZ b')) := by
        have := radialSizeConstant_pos hρ Cr q
        positivity
      refine momentBound_of_le hLaw hρ hp hΨ (g := fun _ => 0) (hgc b') ?_ ?_ ?_
      · simp
      · intro η hη
        have a1 := hpn η hη b'
        simp only [hb, if_false] at a1
        have a0 : 0 ≤ bondGradNorm (fun η : BondField ι => radialTerm p (η b)) b' η := norm_nonneg _
        have a2 : bondGradNorm (fun η : BondField ι => radialTerm p (η b)) b' η = 0 := le_antisymm a1 a0
        rw [a2, abs_zero, zero_pow (by omega)]
      · have : ballExpectation (cutoffFactor ρ p) Ψ (fun _ : BondField ι => (0 : ℝ)) = 0 := by
          simp [ballExpectation]
        rw [this]
        positivity
end Sizes
theorem vecCons_single_one {k : ℕ} (a : Fin k) :
    (![Pi.single a 1] : Fin 1 → Fin k → ℝ) = fun l => Pi.single ((![a] : Fin 1 → Fin k) l) 1 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.basisVectors_one <;> assumption
theorem vecCons_single_two {k : ℕ} (a b : Fin k) :
    (![Pi.single a 1, Pi.single b 1] : Fin 2 → Fin k → ℝ) =
      fun l => Pi.single ((![a, b] : Fin 2 → Fin k) l) 1 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.basisVectors_two <;> assumption
theorem bondSpan_le (hsym : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a)
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d) {k : ℕ} (Y : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) (R : ℕ) (hall : ∀ l, cellSupDist Y (c l).1 ≤ R) : bondSpan Y c ≤ 2 * R := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.bondSpan_le_two_mul <;> assumption
theorem exp_decay_product_le {κ n s D d₁ d₂ d₃ : ℝ} (hκ : 0 ≤ κ) (hn : n ≤ 2 * (s + D + d₁ + d₂ + d₃))
    (hs : 0 ≤ s) (hD : 0 ≤ D) (h1 : 0 ≤ d₁) (h2 : 0 ≤ d₂) (h3 : 0 ≤ d₃) :
    Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (-(2 ^ 3 * κ * d₁)) * Real.exp (-(2 ^ 3 * κ * d₂)) *
        Real.exp (-(2 ^ 3 * κ * d₃)) * Real.exp (-(κ / 8 * D)) ≤ Real.exp (-(κ / 2 ^ 5 * n)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.exp_product_le <;> assumption
section Terms
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def CumulantBounds (ρ x κ T₀ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (y : ι → F.Cell) : Prop :=
  ∀ (M : ℕ) (H : Fin M → BondField ι → ℝ) (Z : Fin M → F.Cell) (hh : Fin M → ℝ) (C : Fin M → ℕ → ℝ),
    2 ≤ M → M ≤ 9 → (∀ i, ContDiffOn ℝ 1 (H i) {η | ∀ b, ‖η b‖ < ρ}) → (∀ i, 0 ≤ hh i) → (∀ i q, 0 ≤ C i q) →
    (∀ i, HasLocalSize ρ r Ψ (C i) x κ (hh i) (fun b => (cellSupDist (y b) (Z i) : ℝ)) (H i)) →
    |cumulantFromMoments r Ψ H| ≤ T₀ * (∏ i, (sizeConstantSum (C i) M * hh i)) *
      Real.exp (-(κ / 8 * cellsDiameter Z))
variable {ρ x κ T₀ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} {y : ι → F.Cell}
structure LocatedObservable (ρ x κ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (y : ι → F.Cell) (C : ℕ → ℝ) (a : ℝ)
    (Z : F.Cell) (G : BondField ι → ℝ) : Prop where
  smooth : ContDiffOn ℝ 1 G {η | ∀ b, ‖η b‖ < ρ}
  hasLocalSize : HasLocalSize ρ r Ψ C x κ a (fun b => (cellSupDist (y b) Z : ℝ)) G
  amplitude_nonneg : 0 ≤ a
  constant_nonneg : ∀ q, 0 ≤ C q
theorem abs_ballCovariance_le (cb : CumulantBounds ρ x κ T₀ r Ψ y)
    (he : ∀ H : Fin 2 → BondField ι → ℝ, cumulantFromMoments r Ψ H = ballCovariance r Ψ (H 0) (H 1))
    {C₀ C₁ : ℕ → ℝ} {a₀ a₁ : ℝ} {Z₀ Z₁ : F.Cell} {G₀ G₁ : BondField ι → ℝ}
    (o₀ : LocatedObservable ρ x κ r Ψ y C₀ a₀ Z₀ G₀) (o₁ : LocatedObservable ρ x κ r Ψ y C₁ a₁ Z₁ G₁) :
    |ballCovariance r Ψ G₀ G₁| ≤ T₀ * ((sizeConstantSum C₀ 2 * a₀) * (sizeConstantSum C₁ 2 * a₁)) *
      Real.exp (-(κ / 8 * cellsDiameter ![Z₀, Z₁])) := by
  have := cb 2 ![G₀, G₁] ![Z₀, Z₁] ![a₀, a₁] ![C₀, C₁] le_rfl (by norm_num)
    (fun i => by fin_cases i; exacts [o₀.smooth, o₁.smooth])
    (fun i => by fin_cases i; exacts [o₀.amplitude_nonneg, o₁.amplitude_nonneg])
    (fun i q => by fin_cases i; exacts [o₀.constant_nonneg q, o₁.constant_nonneg q])
    (fun i => by fin_cases i; exacts [o₀.hasLocalSize, o₁.hasLocalSize])
  rw [he] at this
  simpa [Fin.prod_univ_two] using this
theorem abs_ballThirdCumulant_le (cb : CumulantBounds ρ x κ T₀ r Ψ y)
    (he : ∀ H : Fin 3 → BondField ι → ℝ, cumulantFromMoments r Ψ H = ballThirdCumulant r Ψ (H 0) (H 1) (H 2))
    {C₀ C₁ C₂ : ℕ → ℝ} {a₀ a₁ a₂ : ℝ} {Z₀ Z₁ Z₂ : F.Cell} {G₀ G₁ G₂ : BondField ι → ℝ}
    (o₀ : LocatedObservable ρ x κ r Ψ y C₀ a₀ Z₀ G₀) (o₁ : LocatedObservable ρ x κ r Ψ y C₁ a₁ Z₁ G₁)
    (o₂ : LocatedObservable ρ x κ r Ψ y C₂ a₂ Z₂ G₂) :
    |ballThirdCumulant r Ψ G₀ G₁ G₂| ≤ T₀ * ((sizeConstantSum C₀ 3 * a₀) * (sizeConstantSum C₁ 3 * a₁) *
      (sizeConstantSum C₂ 3 * a₂)) * Real.exp (-(κ / 8 * cellsDiameter ![Z₀, Z₁, Z₂])) := by
  have := cb 3 ![G₀, G₁, G₂] ![Z₀, Z₁, Z₂] ![a₀, a₁, a₂] ![C₀, C₁, C₂] (by norm_num) (by norm_num)
    (fun i => by fin_cases i; exacts [o₀.smooth, o₁.smooth, o₂.smooth])
    (fun i => by fin_cases i; exacts [o₀.amplitude_nonneg, o₁.amplitude_nonneg, o₂.amplitude_nonneg])
    (fun i q => by fin_cases i; exacts [o₀.constant_nonneg q, o₁.constant_nonneg q, o₂.constant_nonneg q])
    (fun i => by fin_cases i; exacts [o₀.hasLocalSize, o₁.hasLocalSize, o₂.hasLocalSize])
  rw [he] at this
  simpa [Fin.prod_univ_three] using this
end Terms
theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
def translatedExponent (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) η -
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)
theorem exponent_eq_sum (hEnds : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) {x : ℝ} {f : LocalFamily}
    {V' : F.GaugeField F.top}
    (hX : CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < T.ballRadius) :
    (coldHalfLawAt T x f).exponent V' η =
      ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y V' η -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η V' := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.coldHalfLaw_exponent_eq <;> assumption
theorem translated_expectation (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hEnds : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hρ : 0 < T.ballRadius)
    (hcut : IsCutoff T.ballRadius T.p) {x : ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top} (K : AboveFrames F) (hfin : Finite F.Cell)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (hXc : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (hR : CentredExpansionBounds false T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L
      (frameRadius x) f V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hK : ∀ (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        K q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η)) :
    ∃ (B : Set (Fin k → ℝ)) (Kb : ℝ), IsOpen B ∧ B ∈ 𝓝 (0 : Fin k → ℝ) ∧
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 3 B Kb (translatedExponent T x f V c X) ∧
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 3 B Kb
        (fun τ η => K η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) ∧
      ∀ τ ∈ B, (coldHalfLawAt T x f).expectationOf K (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) =
        gibbsMean (cutoffLaw F T.ballRadius T.p) (translatedExponent T x f V c X τ)
          (fun η => K η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) := by
  classical
  set Sv := StepVariable (finiteCells F) with hSv
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F T.ballRadius T.p hρ hcut
  have hμc : ∀ᵐ η ∂cutoffLaw F T.ballRadius T.p, ∀ b, ‖η b‖ ≤ T.ballRadius := by
    filter_upwards [hμb] with η hη b using (hη b).le
  have hEV := hXc V hV
  let Gm : (Fin k → ℝ) × Sv → ℝ := fun z => translatedExponent T x f V c X z.1 z.2
  let Gk : (Fin k → ℝ) × Sv → ℝ := fun z => K z.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X z.1) V)
  have sGm : ∀ η : Sv, (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 3 Gm (0, η) := fun η hη =>
    (ContDiffAt.sum fun Y _ => hEV.smooth Y η k c X hη).sub (ContDiffAt.sum fun y _ => hR.smooth y η k c X hη)
  let π : (Fin k → ℝ) × (ℝ × Sv) → (Fin k → ℝ) × Sv := fun z => (z.1, z.2.2)
  have hπs : ContDiff ℝ 3 π := contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have lift : ∀ {G : (Fin k → ℝ) × Sv → ℝ}, (∀ η : Sv, (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 3 G (0, η)) →
      ∀ (v : ℝ) (η : Sv), (∀ b, ‖η b‖ ≤ T.ballRadius) →
        ContDiffAt ℝ 3 (fun z : (Fin k → ℝ) × (ℝ × Sv) => G (π z)) (0, v, η) := fun {G} hG v η hη =>
    ContDiffAt.comp (g := G) (f := π) (0, v, η) (hG η hη) hπs.contDiffAt
  obtain ⟨r₁, M₁, hr₁, hD₁⟩ := hDom _ k T.ballRadius (cutoffLaw F T.ballRadius T.p) (fun z => Gm (π z)) hμc
    (fun v η _ hη => lift sGm v η hη)
  obtain ⟨r₂, M₂, hr₂, hD₂⟩ := hDom _ k T.ballRadius (cutoffLaw F T.ballRadius T.p) (fun z => Gk (π z)) hμc
    (fun v η _ hη => lift hK v η hη)
  obtain ⟨r₀, hr₀, hcold⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_isSmallCurvature_leftTranslate hfin c X hV)
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have dom_mono : ∀ {r M r' M' : ℝ} {G : (Fin k → ℝ) → Sv → ℝ}, r' ≤ r → M ≤ M' →
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 3 (Metric.ball 0 r) M G →
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 3 (Metric.ball 0 r') M' G :=
    fun {r M r' M' G} hr hM h => by
    have hB := Metric.ball_subset_ball (x := (0 : Fin k → ℝ)) hr
    refine ⟨fun τ hτ => h.aestronglyMeasurable τ (hB hτ), ?_, ?_⟩
    · filter_upwards [h.contDiffOn] with ω hω using hω.mono hB
    · filter_upwards [h.norm_iteratedFDeriv_le] with ω hω j hj τ hτ using le_trans (hω j hj τ (hB hτ)) hM
  set r : ℝ := min r₀ (min r₁ r₂) with hr
  have hrpos : 0 < r := lt_min hr₀ (lt_min hr₁ hr₂)
  refine ⟨Metric.ball 0 r, max M₁ M₂, Metric.isOpen_ball, Metric.ball_mem_nhds _ hrpos, ?_, ?_, ?_⟩
  · exact dom_mono ((min_le_right _ _).trans (min_le_left _ _)) (le_max_left _ _) (hD₁ 0 h01)
  · exact dom_mono ((min_le_right _ _).trans (min_le_right _ _)) (le_max_right _ _) (hD₂ 0 h01)
  · intro τ hτ
    have hc := hcold τ (Metric.ball_subset_ball (min_le_left _ _) hτ)
    show cutoffMean T.ballRadius T.p _ _ = _
    rw [hμm]
    apply gibbsMean_congr_ae
    · filter_upwards [hμb] with η hη
      exact exponent_eq_sum hEnds T (hXc _ hc) η hη
    · exact Filter.EventuallyEq.rfl
theorem cellSupDist_le_cellsDiameter {M : ℕ} (Z : Fin M → F.Cell) (i j : Fin M) :
    cellSupDist (Z i) (Z j) ≤ cellsDiameter Z := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.cellSupDist_le_cellsDiameter <;> assumption
theorem cellSupDist_le_add_bondListDiameter
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d) {j : ℕ}
    (c' : Fin j → F.Site F.top × Fin 4) (Y : F.Cell) (l₀ m : Fin j) :
    cellSupDist Y (c' m).1 ≤ cellSupDist Y (c' l₀).1 + _root_.YangMills.Construction.BlockAverages.bondListDiameter c' := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.cellSupDist_le_add_bondListDiameter <;> assumption
theorem sizeConstantSum_mono {C : ℕ → ℝ} (hC : ∀ q, 0 ≤ C q) {M : ℕ} (hM : M ≤ 4) :
    sizeConstantSum C M ≤ sizeConstantSum C 4 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.sizeConstantSum_le_four <;> assumption
theorem one_le_sizeConstantSum {C : ℕ → ℝ} (hC : ∀ q, 0 ≤ C q) (M : ℕ) : 1 ≤ sizeConstantSum C M := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.one_le_sizeConstantSum <;> assumption
theorem covariance_product_le {T₀ c₀ c₁ A h E₀ E₁ ED cK cP E : ℝ} (hT : 0 ≤ T₀) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (h₀ : c₀ ≤ cK) (h₁ : c₁ ≤ cP) (hcP : 1 ≤ cP) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hED : 0 ≤ ED)
    (hE : E₀ * E₁ * ED ≤ E) :
    T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁))) * ED ≤ T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.second_order_product_le <;> assumption
theorem thirdCumulant_product_le {T₀ c₀ c₁ c₂ A h E₀ E₁ E₂ ED cK cP E : ℝ} (hT : 0 ≤ T₀) (hh : 0 ≤ h)
    (hA : 0 ≤ A) (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h₀ : c₀ ≤ cK) (h₁ : c₁ ≤ cP) (h₂ : c₂ ≤ cP) (hcP : 1 ≤ cP) (hE₀ : 0 ≤ E₀)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hED : 0 ≤ ED) (hE : E₀ * E₁ * E₂ * ED ≤ E) :
    T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁)) * (c₂ * (A * E₂))) * ED ≤
      T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.third_order_product_le <;> assumption
theorem cutoffTerm_expectation_bound (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hMean : TiltedMeanDifferentiation) (hEnds : interpolationAtEndpoints)
    (hExp : lowOrderCumulantFormulas) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hρ : 0 < T.ballRadius) (hcut : IsCutoff T.ballRadius T.p)
    (hκ : 0 < T.κ)
    {Cq Cp : ℕ → ℝ} (hCq : ∀ q, 0 ≤ Cq q) (hCp : ∀ q, 0 ≤ Cp q) {A T₀ a : ℝ} (hA : 0 ≤ A) (hT₀ : 0 ≤ T₀)
    (ha : 0 ≤ a) {t : ℕ}
    {x : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell}
    (hst : IsAdmissibleAt T t x f F V) (hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f)
    (hfin : Finite F.Cell) (hsym : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a)
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d)
    (Ψ' : StepVariable (finiteCells F) → ℝ)
    (hd : ballDensity (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ')
    (hz : ∀ η : BondField ↥(chordBonds (finiteCells F)), ¬ (∀ b, ‖η b‖ < T.ballRadius) →
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0)
    (cb : CumulantBounds T.ballRadius x T.κ T₀ (cutoffFactor T.ballRadius T.p) Ψ'
      (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1))
    (hXc : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (hR : CentredExpansionBounds false T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L
      (frameRadius x) f V)
    (hEL : IsLocalExponentAt T Cp A) (G : StepVariable (finiteCells F) → ℝ)
    (hGd : (coldHalfLawAt T x f).cutoffTerm Y = fun η _ => G η) (hGm : Measurable G)
    (hGμ : Integrable G (cutoffLaw F T.ballRadius T.p))
    (hG0 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → 0 ≤ G η)
    (hobs : LocatedObservable T.ballRadius x T.κ (cutoffFactor T.ballRadius T.p) Ψ'
      (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) Cq a Y G) :
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun τ : Fin k → ℝ =>
        (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).cutoffTerm Y)
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) ∧
    ∀ (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).cutoffTerm Y)) V c X| ≤
        (2 * (T₀ * (sizeConstantSum Cq 4 * (sizeConstantSum Cp 4 * (1 + A)) ^ 3))) * a *
          Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) := by
  classical
  set Q := coldHalfLawAt T x f with hQ
  set r := cutoffFactor T.ballRadius T.p with hr
  set y : ↥(chordBonds (finiteCells F)) → F.Cell := fun b => enclosingCell b.1.1 with hy
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F T.ballRadius T.p hρ hcut
  have := hfinμ
  set μ := cutoffLaw F T.ballRadius T.p with hμ
  set ν := μ.withDensity fun η => ENNReal.ofReal |G η| with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hGμ.abs.2
  have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have sm : ∀ A₀ g : StepVariable (finiteCells F) → ℝ,
      _root_.YangMills.Construction.TiltedMeans.tiltedMean ν μ A₀ g = gibbsMean μ A₀ (fun η => G η * g η) := by
    intro A₀ g
    unfold _root_.YangMills.Construction.TiltedMeans.tiltedMean gibbsMean
    congr 1
    rw [hν, integral_withDensity_eq_integral_toReal_smul hGm.abs.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hμb] with η hη
    simp only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
    rw [abs_of_nonneg (hG0 η hη)]
    ring
  have hmain : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ∃ (B : Set (Fin k → ℝ)) (Kb : ℝ), IsOpen B ∧ B ∈ 𝓝 (0 : Fin k → ℝ) ∧
        IsDominatedSmoothFamily μ 3 B Kb (translatedExponent T x f V c X) ∧
        IsDominatedSmoothFamily μ 3 B Kb (fun (_ : Fin k → ℝ) (_ : StepVariable (finiteCells F)) => (1 : ℝ)) ∧
        (fun τ : Fin k → ℝ => Q.expectationOf (Q.cutoffTerm Y) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) =ᶠ[𝓝 0]
          fun τ => _root_.YangMills.Construction.TiltedMeans.tiltedMean ν μ (translatedExponent T x f V c X τ) (fun _ => 1) := by
    intro k c X
    obtain ⟨B, Kb, hBo, hB0, dA, dH, -⟩ := translated_expectation (f := f) hRim hDom hEnds T hρ hcut
      (fun _ _ => (1 : ℝ)) hfin hst.small_curvature hXc hR c X (fun η hη => contDiffAt_const)
    refine ⟨B, Kb, hBo, hB0, dA, dH, ?_⟩
    filter_upwards [eventually_isSmallCurvature_leftTranslate hfin c X hst.small_curvature] with τ hτ
    rw [sm]
    show cutoffMean T.ballRadius T.p _ _ = _
    rw [hμm]
    apply gibbsMean_congr_ae
    · filter_upwards [hμb] with η hη
      exact exponent_eq_sum hEnds T (hXc _ hτ) η hη
    · refine Filter.Eventually.of_forall fun η => ?_
      show Q.cutoffTerm Y η _ = _
      rw [hGd]
      simp
  refine ⟨fun k c X => ?_, fun c X hX => ?_⟩
  · obtain ⟨B, Kb, hBo, hB0, dA, dH, ev⟩ := hmain c X
    obtain ⟨hcd, -⟩ := hMean _ ν μ k B Kb _ _ hBo hμ0 hac dA dH
    exact ((hcd.contDiffAt hB0).of_le (by norm_num)).congr_of_eventuallyEq ev
  obtain ⟨B, Kb, hBo, hB0, dA, dH, ev⟩ := hmain c X
  obtain ⟨hcd, hform⟩ := hMean _ ν μ 2 B Kb _ _ hBo hμ0 hac dA dH
  have h0B : (0 : Fin 2 → ℝ) ∈ B := mem_of_mem_nhds hB0
  let Af := translatedExponent T x f V c X
  let units : ∀ {j : ℕ}, (Fin j → Fin 2) → Fin j → Fin 2 → ℝ := fun ι l => Pi.single (ι l) 1
  let GA : ∀ {j : ℕ}, (Fin j → Fin 2) → StepVariable (finiteCells F) → ℝ :=
    fun ι => paramIteratedDeriv Af (units ι) 0
  have hO : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} =
        ⋂ b, {η : StepVariable (finiteCells F) | ‖η b‖ < T.ballRadius} := by
      ext η; simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have hline : ∀ {G₁ : (Fin 2 → ℝ) × StepVariable (finiteCells F) → ℝ} {η : StepVariable (finiteCells F)},
      ContDiffAt ℝ 3 G₁ (0, η) → ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ => G₁ (τ, η)) 0 := fun {G₁ η} hG =>
    ContDiffAt.comp (g := G₁) (f := fun τ : Fin 2 → ℝ => (τ, η)) 0 hG
      ((contDiff_id.prodMk contDiff_const).contDiffAt)
  have hofle : ∀ {j : ℕ}, j ≤ 3 → ((j : ℕ) : WithTop ℕ∞) ≤ 3 := fun {j} hj => by exact_mod_cast hj
  have hwm : ∀ g : StepVariable (finiteCells F) → ℝ, gibbsMean μ (Af 0) g = ballExpectation r Ψ' g := by
    intro g
    have e1 : gibbsMean μ (Af 0) g = gibbsMean μ (Q.exponent V) g := by
      refine gibbsMean_congr_ae ?_ Filter.EventuallyEq.rfl
      filter_upwards [hμb] with η hη
      have := exponent_eq_sum (f := f) hEnds T (hXc V hst.small_curvature) η hη
      simp only [Af, translatedExponent, leftTranslate_bondSpread_zero]
      exact this.symm
    rw [e1, ← hμm]
    show ballExpectation r (Q.exponent V) g = _
    unfold ballExpectation
    rw [hd]
  have eqA : ∀ {j : ℕ} (ι : Fin j → Fin 2), j ≤ 3 → ∀ η : StepVariable (finiteCells F),
      (∀ b, ‖η b‖ < T.ballRadius) →
      bondDeriv (fun V' => Q.exponent V' η) V (c ∘ ι) (X ∘ ι) = GA ι η := by
    intro j ι hj3 η hη
    have ev' : (fun τ : Fin 2 → ℝ => Q.exponent (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) η) =ᶠ[𝓝 0]
        fun τ => Af τ η := by
      filter_upwards [eventually_isSmallCurvature_leftTranslate hfin c X hst.small_curvature] with τ hτ
      exact exponent_eq_sum hEnds T (hXc _ hτ) η hη
    have smA : ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ => Af τ η) 0 := by
      have h1 := (ContDiffAt.sum fun Y' _ =>
          hline ((hXc V hst.small_curvature).smooth Y' η 2 c X fun b => (hη b).le) :
        ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ => ∑ Y' ∈ finiteCells F,
          cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y'
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) η) 0)
      have h2 := (ContDiffAt.sum fun y' _ => hline (hR.smooth y' η 2 c X fun b => (hη b).le) :
        ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ => ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
          centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y' η
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0)
      exact h1.sub h2
    have smE : ContDiffAt ℝ j (fun τ : Fin 2 → ℝ => Q.exponent (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) η) 0 :=
      (smA.congr_of_eventuallyEq ev').of_le (hofle hj3)
    have e1 := (Filter.EventuallyEq.iteratedFDeriv ℝ ev' j).eq_of_nhds
    rw [← iteratedFDeriv_single_eq_bondDeriv (fun V' => Q.exponent V' η) V c X ι smE, e1]
    rfl
  have obsA : ∀ {j : ℕ} (ι : Fin j → Fin 2) (l₀ : Fin j), j ≤ 2 →
      LocatedObservable T.ballRadius x T.κ r Ψ' y Cp (A * Real.exp (-(2 ^ 3 * T.κ * _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι))))
        (c (ι l₀)).1 (GA ι) := by
    intro j ι l₀ hj
    have hu : AreUnitVectors (X ∘ ι) := fun l => hX (ι l)
    obtain ⟨hc1, hs1⟩ := hEL t x f F V j (c ∘ ι) (X ∘ ι) l₀ hst hrow hj hu
    have eqb := eqA ι (by omega : j ≤ 3)
    refine ⟨hc1.congr fun η hη => (eqb η hη).symm, ?_, by positivity, hCp⟩
    exact hasLocalSize_congr_of_eqOn_balls hO (fun η hη => by
        show ballDensity r Ψ' η = 0
        exact hz η hη) eqb (hasLocalSize_congr_density hd hs1)
  set cK := sizeConstantSum Cq 4 with hcK
  set cP := sizeConstantSum Cp 4 with hcP
  have hcP1 : 1 ≤ cP := one_le_sizeConstantSum hCp 4
  have hκ0 := hκ.le
  have hc0 : ∀ (C : ℕ → ℝ) (M : ℕ), (∀ q, 0 ≤ C q) → 0 ≤ sizeConstantSum C M := fun C M hC =>
    le_trans zero_le_one (one_le_sizeConstantSum hC M)
  set E : ℝ := Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) with hEdef
  set b : ℝ := T₀ * (cK * (cP * (1 + A)) ^ 3) * a * E with hb
  obtain ⟨he2, he3, -⟩ := hExp _ r Ψ'
  have hobs1 : LocatedObservable T.ballRadius x T.κ r Ψ' y Cq (a * 1) Y G := by simpa using hobs
  have hz0 : Real.exp (-(2 ^ 3 * T.κ * (0 : ℝ))) = 1 := by simp
  have hz5 : Real.exp (-(2 ^ 5 * T.κ * (0 : ℝ))) = 1 := by simp
  have t2 : ∀ {j₁ : ℕ} (ι₁ : Fin j₁ → Fin 2) (l₁ : Fin j₁), j₁ ≤ 2 → (∀ l : Fin 2, ∃ m, ι₁ m = l) →
      |ballCovariance r Ψ' G (GA ι₁)| ≤ b := by
    intro j₁ ι₁ l₁ h₁ hcov
    have hc := abs_ballCovariance_le cb he2 hobs1 (obsA ι₁ l₁ h₁)
    refine hc.trans ?_
    set d₁ := _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι₁)
    set D := cellsDiameter ![Y, (c (ι₁ l₁)).1]
    have hall : ∀ l, cellSupDist Y (c l).1 ≤ D + d₁ := by
      intro l
      obtain ⟨m', rfl⟩ := hcov l
      have h1 := cellSupDist_le_add_bondListDiameter htri (c ∘ ι₁) Y l₁ m'
      have h2 := cellSupDist_le_cellsDiameter ![Y, (c (ι₁ l₁)).1] 0 1
      simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
      omega
    have hn := bondSpan_le hsym htri Y c _ hall
    have hn' : (bondSpan Y c : ℝ) ≤ 2 * ((0 : ℝ) + D + d₁ + 0 + 0) := by
      have : (bondSpan Y c : ℝ) ≤ ((2 * (D + d₁) : ℕ) : ℝ) := Nat.cast_le.2 hn
      push_cast at this
      linarith
    have hE := exp_decay_product_le hκ0 hn' le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _) le_rfl le_rfl
    rw [hz5, hz0, mul_one, mul_one] at hE
    exact covariance_product_le hT₀ ha hA (hc0 _ _ hCq) (hc0 _ _ hCp) (sizeConstantSum_mono hCq (by norm_num))
      (sizeConstantSum_mono hCp (by norm_num)) hcP1 zero_le_one (Real.exp_pos _).le (Real.exp_pos _).le hE
  have t3 : ∀ {j₁ j₂ : ℕ} (ι₁ : Fin j₁ → Fin 2) (ι₂ : Fin j₂ → Fin 2) (l₁ : Fin j₁) (l₂ : Fin j₂), j₁ ≤ 2 →
      j₂ ≤ 2 →
      (∀ l : Fin 2, (∃ m, ι₁ m = l) ∨ (∃ m, ι₂ m = l)) → |ballThirdCumulant r Ψ' G (GA ι₁) (GA ι₂)| ≤ b := by
    intro j₁ j₂ ι₁ ι₂ l₁ l₂ h₁ h₂ hcov
    have hc := abs_ballThirdCumulant_le cb he3 hobs1 (obsA ι₁ l₁ h₁) (obsA ι₂ l₂ h₂)
    refine hc.trans ?_
    set d₁ := _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι₁)
    set d₂ := _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι₂)
    set D := cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1]
    have hall : ∀ l, cellSupDist Y (c l).1 ≤ D + d₁ + d₂ := by
      intro l
      rcases hcov l with ⟨m', rfl⟩ | ⟨m', rfl⟩
      · have h1 := cellSupDist_le_add_bondListDiameter htri (c ∘ ι₁) Y l₁ m'
        have h2 := cellSupDist_le_cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1] 0 1
        simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
        omega
      · have h1 := cellSupDist_le_add_bondListDiameter htri (c ∘ ι₂) Y l₂ m'
        have h2 := cellSupDist_le_cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1] 0 2
        simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val] at h1 h2
        omega
    have hn := bondSpan_le hsym htri Y c _ hall
    have hn' : (bondSpan Y c : ℝ) ≤ 2 * ((0 : ℝ) + D + d₁ + d₂ + 0) := by
      have : (bondSpan Y c : ℝ) ≤ ((2 * (D + d₁ + d₂) : ℕ) : ℝ) := Nat.cast_le.2 hn
      push_cast at this
      linarith
    have hE := exp_decay_product_le hκ0 hn' le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) le_rfl
    rw [hz5, hz0, mul_one, one_mul] at hE
    have hE' : 1 * Real.exp (-(2 ^ 3 * T.κ * (d₁ : ℝ))) * Real.exp (-(2 ^ 3 * T.κ * (d₂ : ℝ))) *
        Real.exp (-(T.κ / 8 * (D : ℝ))) ≤ E := by simpa using hE
    exact thirdCumulant_product_le hT₀ ha hA (hc0 _ _ hCq) (hc0 _ _ hCp) (hc0 _ _ hCp)
      (sizeConstantSum_mono hCq (by norm_num))
      (sizeConstantSum_mono hCp (by norm_num)) (sizeConstantSum_mono hCp (by norm_num)) hcP1 zero_le_one
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le hE'
  have hA1 : ∀ d : Fin 2, paramIteratedDeriv Af ![Pi.single d 1] 0 = GA ![d] := fun d => by
    show _ = paramIteratedDeriv Af (units ![d]) 0
    simp only [units]
    rw [vecCons_single_one]
  have hA2 : ∀ d e : Fin 2, paramIteratedDeriv Af ![Pi.single d 1, Pi.single e 1] 0 = GA ![d, e] := fun d e => by
    show _ = paramIteratedDeriv Af (units ![d, e]) 0
    simp only [units]
    rw [vecCons_single_two]
  have hMeq : bondDeriv (Q.expectationOf (Q.cutoffTerm Y)) V c X =
      iteratedFDeriv ℝ 2 (fun τ => _root_.YangMills.Construction.TiltedMeans.tiltedMean ν μ (Af τ) (fun _ => 1)) 0 (fun l => Pi.single l 1) := by
    have e1 := (Filter.EventuallyEq.iteratedFDeriv ℝ ev 2).eq_of_nhds
    unfold bondDeriv
    rw [e1]
  let Hc : (Fin 2 → ℝ) → StepVariable (finiteCells F) → ℝ := fun _ _ => 1
  have hH0 : ∀ {j : ℕ} (w : Fin j → Fin 2 → ℝ), j ≠ 0 → paramIteratedDeriv Hc w 0 = fun _ => 0 := by
    intro j w hj
    funext η
    simp only [paramIteratedDeriv, Hc]
    rw [iteratedFDeriv_const_of_ne hj]
    rfl
  have sc0 : ∀ g : StepVariable (finiteCells F) → ℝ, tiltedCov ν μ (Af 0) (fun _ => 0) g = 0 := fun g => by
    simp [tiltedCov, _root_.YangMills.Construction.TiltedMeans.tiltedMean]
  have sc1 : ∀ g : StepVariable (finiteCells F) → ℝ,
      tiltedCov ν μ (Af 0) (fun _ => 1) g = ballCovariance r Ψ' G g := fun g => by
    unfold tiltedCov ballCovariance
    rw [sm, sm, hwm, hwm, hwm]
    simp
  have st1 : ∀ g h : StepVariable (finiteCells F) → ℝ, tiltedCumulantThree ν μ (Af 0) (fun _ => 1) g h =
      ballThirdCumulant r Ψ' G g h := fun g h => by
    unfold tiltedCumulantThree ballThirdCumulant
    simp only [sm, hwm]
    simp only [one_mul, mul_one]
    have e : (fun η => G η * (g η * h η)) = fun η => G η * g η * h η := by
      funext η
      ring
    rw [e]
  have u2 : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
    funext l; fin_cases l <;> rfl
  have F2 := (hform 0 h0B (Pi.single 1 1) (Pi.single 0 1) 0).2.1
  have hF2 : iteratedFDeriv ℝ 2 (fun τ => _root_.YangMills.Construction.TiltedMeans.tiltedMean ν μ (Af τ) (fun _ => 1)) 0 ![Pi.single 0 1, Pi.single 1 1] =
      - ballCovariance r Ψ' G (GA ![0, 1]) + ballThirdCumulant r Ψ' G (GA ![1]) (GA ![0]) := by
    have e1 : paramIteratedDeriv (fun (_ : Fin 2 → ℝ) (_ : StepVariable (finiteCells F)) => (1 : ℝ))
        ![Pi.single 0 1, Pi.single 1 1] 0 = fun _ => 0 := hH0 _ (by norm_num)
    have e2 : ∀ d : Fin 2, paramIteratedDeriv (fun (_ : Fin 2 → ℝ) (_ : StepVariable (finiteCells F)) => (1 : ℝ))
        ![(Pi.single d 1 : Fin 2 → ℝ)] 0 = fun _ => 0 := fun d => hH0 _ (by norm_num)
    have e3 := F2
    rw [e1, e2, e2] at e3
    refine e3.trans ?_
    show _root_.YangMills.Construction.TiltedMeans.tiltedMean ν μ (Af 0) (fun _ => 0) -
      tiltedCov ν μ (Af 0) (fun _ => 0) (paramIteratedDeriv Af ![Pi.single 0 1] 0) -
      tiltedCov ν μ (Af 0) (fun _ => 0) (paramIteratedDeriv Af ![Pi.single 1 1] 0) -
      tiltedCov ν μ (Af 0) (fun _ => 1) (paramIteratedDeriv Af ![Pi.single 0 1, Pi.single 1 1] 0) +
      tiltedCumulantThree ν μ (Af 0) (fun _ => 1) (paramIteratedDeriv Af ![Pi.single 1 1] 0)
        (paramIteratedDeriv Af ![Pi.single 0 1] 0) = _
    rw [sc0, sc0, sc1, st1, hA2, hA1, hA1]
    simp [_root_.YangMills.Construction.TiltedMeans.tiltedMean]
  rw [hMeq, u2, hF2]
  have hrhs : (2 * (T₀ * (cK * (cP * (1 + A)) ^ 3))) * a * E = 2 * b := by
    rw [hb]; ring
  rw [hrhs]
  have a1 := abs_le.1 (t2 ![0, 1] 0 (by norm_num) (by decide))
  have a2 := abs_le.1 (t3 ![1] ![0] 0 0 (by norm_num) (by norm_num) (by decide))
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a1.1, a1.2, a2.1, a2.2]
end CutoffTermMean
open CutoffTermMean in
theorem cutoffTermExpectation (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hMean : TiltedMeanDifferentiation) (hEnds : interpolationAtEndpoints)
    (hExp : lowOrderCumulantFormulas) (hEL : exponentLocalityStatement)
    (hCum : cumulantDecayBound) (hFew : cellBondsCardStatement)
    (hLaw : normalizedBallLawIsProbabilityStatement) (hFB : interpolatedFramesStatement)
    (hB : CellExponentsBounded) (hRw : CentredExpansionsBounded)
    (hG : CubicTorusCellGeometry) (hJ : EventuallyInParametersCombines) (hPow : cutoffDerivBoundsStatement)
    (hS : FiniteSumSizeBound) : cutoffTermExpectationStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cm, Cz, Cr, hP⟩ := hFB
  obtain ⟨Cp, A, hCp, hA, hLoc⟩ := hEL
  obtain ⟨hg1, -⟩ := hG
  choose! T₀ hT₀ hT₀' using hCum
  have h64 : EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨fun U => |(2 * (T₀ (4 * U.L ^ 4) U.κ U.chainParams.lam *
      (sizeConstantSum (radialSizeConstant U.ballRadius (Cr (momentParameters U))) 4 *
      (sizeConstantSum (Cp (sizeParameters U)) 4 * (1 + A U)) ^ 3))) * ((4 * U.L ^ 4 : ℕ) : ℝ)|,
    fun T => abs_nonneg _, ?_⟩
  refine weaken _ _ ?_ (join _ _ hP (join _ _ h64 (join _ _ hLoc (join _ _ hB hRw))))
  rintro T hDr ⟨hPT, ⟨h64', hy1⟩, hLocT, hXb, hRb⟩
  intro t x f F V Y hst hrow
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hx : 0 < x := by linarith
  have hPT' := hPT t x hfl
  set Q := coldHalfLawAt T x f with hQ
  let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop V (Q.exponent V)
  have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
      (frameRadius x) (chordBondDist F) :=
    ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
      Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hconv, hmoms, -⟩ := hPT'.laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => M)
    ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
  rw [convexCombinationExponent_lawAtTop] at hconv hmoms
  obtain ⟨Ψ', K', hΨ', hconvex, hslope, -⟩ := hconv
  have hΨc : Continuous Ψ' := hconvex.smooth.continuous
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ : 0 < T.κ := hDr.κ_pos
  have hlam : 0 < T.chainParams.lam := hDr.chain_admissible.positivity.2.2.1
  obtain ⟨-, -, -, -, hdm, hdens0, -, -, -, hnz, -⟩ := hLaw _ T.ballRadius T.p Ψ' hρ hDr.cutoff hΨc
  have hz : ∀ η : BondField ↥(chordBonds (finiteCells F)), ¬ (∀ b, ‖η b‖ < T.ballRadius) →
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0 := fun η hη => by
    by_contra hne
    exact hη ((hnz η).1 hne)
  have hd : ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' := by
    funext η
    by_cases hη' : ∀ b, ‖η b‖ < T.ballRadius
    · unfold ballDensity
      rw [hΨ' η hη']
    · have h0 := hz η hη'
      have h1 : radialWeightProd (cutoffFactor T.ballRadius T.p) η = 0 := by
        unfold ballDensity at h0
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      rw [h0]
      unfold ballDensity
      rw [h1, zero_mul]
  obtain ⟨hLF, htt, n, hside, hn⟩ := hst.torus
  have hnpos : 64 ≤ n := h64'.trans hn
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hcub : IsLargeCubicTorus F := ⟨n, hnpos, hside⟩
  have hfin : Finite F.Cell := by
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  obtain ⟨-, -, hsym, htri, -⟩ := hg1 F hoddF hcub
  have hN : ∀ z : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
      4 * T.L ^ 4 := fun z => by
    have := hFew F hoddF (fun i => by rw [hside]; omega) z
    rwa [hLF] at this
  have cb : CumulantBounds T.ballRadius x T.κ (T₀ (4 * T.L ^ 4) T.κ T.chainParams.lam)
      (cutoffFactor T.ballRadius T.p) Ψ'
      (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) :=
    fun M' H Z hh' C h2 h9 hc h0 hq hs =>
      (hT₀' (4 * T.L ^ 4) T.κ T.chainParams.lam hκ hlam F _
        (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) T.ballRadius x T.p Ψ' K'
        hρ hx hDr.cutoff hN hconvex hslope M' H Z hh' C h2 h9 hc h0 hq hs).2
  set r := cutoffFactor T.ballRadius T.p with hr
  set Cb := radialSizeConstant T.ballRadius (Cr (momentParameters T)) with hCb
  have hrim : ∀ (b : ↥(chordBonds (finiteCells F))) (j q N : ℕ), 1 ≤ j → 1 ≤ q →
      Integrable (fun η : BondField ↥(chordBonds (finiteCells F)) =>
        |iteratedDeriv j T.p ‖η b‖| ^ q * ballDensity r Ψ' η) ∧
      ballExpectation r Ψ' (fun η => |iteratedDeriv j T.p ‖η b‖| ^ q) ≤
        Cr (momentParameters T) j q N * (x ^ N)⁻¹ := by
    intro b j q N hj hq
    have h1 := hmoms.cutoff_deriv_moments j q N b hj hq
    have i1 : Integrable (fun η : BondField ↥(chordBonds (finiteCells F)) => |iteratedDeriv j T.p ‖η b‖| ^ q *
        ballDensity r (Q.exponent V) η) := h1.1
    rw [hd] at i1
    refine ⟨i1, ?_⟩
    have h2 : ballExpectation r (Q.exponent V) (fun η => |iteratedDeriv j T.p ‖η b‖| ^ q) ≤
        Cr (momentParameters T) j q N * (x ^ N)⁻¹ := h1.2
    unfold ballExpectation at h2 ⊢
    rw [hd] at h2
    exact h2
  let Sb : Finset ↥(chordBonds (finiteCells F)) := Finset.univ.filter fun b => enclosingCell b.1.1 = Y
  let G : StepVariable (finiteCells F) → ℝ := fun η => ∑ b ∈ Sb, radialTerm T.p (η b)
  have hGd : Q.cutoffTerm Y = fun η _ => G η := by
    funext η V'
    show ColdHalfLaw.sumOverBlock Y _ = _
    unfold ColdHalfLaw.sumOverBlock
    simp only [G, Sb]
    rw [Finset.sum_filter]
    rfl
  have hradm : Measurable (radialTerm T.p) := by
    unfold radialTerm
    exact measurable_norm.mul ((measurable_deriv T.p).comp measurable_norm)
  have hbm : ∀ b : ↥(chordBonds (finiteCells F)),
      Measurable fun η : StepVariable (finiteCells F) => radialTerm T.p (η b) :=
    fun b => hradm.comp (measurable_pi_apply b)
  have hGm : Measurable G := Finset.measurable_fun_sum _ fun b _ => hbm b
  have hrad0 : ∀ v : BondVector, ‖v‖ < T.ballRadius → 0 ≤ radialTerm T.p v := fun v hv => by
    unfold radialTerm
    by_cases h0 : v = 0
    · simp [h0]
    · exact mul_nonneg (norm_nonneg _) ((hPow T.ballRadius T.p hρ hDr.cutoff).1 _ (norm_pos_iff.2 h0) hv)
  have hG0 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → 0 ≤ G η := fun η hη =>
    Finset.sum_nonneg fun b _ => hrad0 _ (hη b)
  have hbd : ∀ b : ↥(chordBonds (finiteCells F)),
      Integrable fun η => radialTerm T.p (η b) * ballDensity r Ψ' η := by
    intro b
    have h1 := (hrim b 1 1 0 le_rfl le_rfl).1
    rw [iteratedDeriv_one] at h1
    refine Integrable.mono' (h1.const_mul T.ballRadius) ((hbm b).mul hdm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)
    by_cases hη : ∀ b, ‖η b‖ < T.ballRadius
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdens0 η)]
      have h2 : |radialTerm T.p (η b)| ≤ T.ballRadius * |deriv T.p ‖η b‖| := by
        unfold radialTerm
        rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_right (hη b).le (abs_nonneg _)
      calc |radialTerm T.p (η b)| * ballDensity r Ψ' η ≤
            T.ballRadius * |deriv T.p ‖η b‖| * ballDensity r Ψ' η :=
            mul_le_mul_of_nonneg_right h2 (hdens0 η)
        _ = _ := by ring
    · rw [hz η hη]
      simp
  have hcomp : IsCompact {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ T.ballRadius} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ T.ballRadius} =
        Set.pi Set.univ fun _ => Metric.closedBall 0 T.ballRadius := by
      ext η
      simp
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨Me, hMe⟩ := hcomp.exists_bound_of_continuousOn (f := fun η => Real.exp (Ψ' η))
    (Real.continuous_exp.comp hΨc).continuousOn
  have hrimeq : ∀ η : StepVariable (finiteCells F),
      cutoffWeight T.ballRadius T.p η = ballDensity r Ψ' η * Real.exp (Ψ' η) := fun η => by
    show radialWeightProd r η = radialWeightProd r η * Real.exp (- Ψ' η) * Real.exp (Ψ' η)
    rw [mul_assoc, ← Real.exp_add]
    simp
  have hrim0 : ∀ η : StepVariable (finiteCells F), 0 ≤ cutoffWeight T.ballRadius T.p η := fun η => by
    rw [hrimeq]
    exact mul_nonneg (hdens0 η) (Real.exp_pos _).le
  have hrimm : Measurable (cutoffWeight (F := F) T.ballRadius T.p) := by
    have : cutoffWeight (F := F) T.ballRadius T.p = fun η => ballDensity r Ψ' η * Real.exp (Ψ' η) :=
      funext hrimeq
    rw [this]
    exact hdm.mul (Real.continuous_exp.comp hΨc).measurable
  have hGρ : Integrable G (cutoffLaw F T.ballRadius T.p) := by
    unfold cutoffLaw
    rw [integrable_withDensity_iff hrimm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hsum : Integrable fun η =>
        ∑ b ∈ Sb, radialTerm T.p (η b) * (ENNReal.ofReal (cutoffWeight T.ballRadius T.p η)).toReal := by
      refine integrable_finsetSum _ fun b _ => ?_
      refine Integrable.mono' ((hbd b).norm.const_mul Me) ?_ (Filter.Eventually.of_forall fun η => ?_)
      · exact ((hbm b).mul hrimm.ennreal_ofReal.ennreal_toReal).aestronglyMeasurable
      · rw [ENNReal.toReal_ofReal (hrim0 η), hrimeq]
        by_cases hη : ∀ b, ‖η b‖ < T.ballRadius
        · have h1 := hMe η fun b => (hη b).le
          rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h1
          rw [← mul_assoc, norm_mul (radialTerm T.p (η b) * ballDensity r Ψ' η),
            Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        · rw [hz η hη]
          simp
    refine hsum.congr (Filter.Eventually.of_forall fun η => ?_)
    show _ = G η * _
    simp only [G]
    rw [Finset.sum_mul]
  have hy0 : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx _
  have hself : ∀ a : F.Cell, cellSupDist a a = 0 := fun a => by simp [cellSupDist]
  let dZ₀ : ↥(chordBonds (finiteCells F)) → ℝ := fun b => (cellSupDist (enclosingCell b.1.1) Y : ℝ)
  have hCbp : ∀ q, 0 < Cb q := fun q => radialSizeConstant_pos hρ _ q
  have hcard : (Sb.card : ℝ) ≤ ((4 * T.L ^ 4 : ℕ) : ℝ) := by exact_mod_cast hN Y
  have hsize := hS _ _ Sb T.ballRadius x T.κ (((4 * T.L ^ 4 : ℕ) : ℝ) * x ^ (-(1 / 2) : ℝ)) T.p Ψ' Cb
    (fun b η => radialTerm T.p (η b))
    (fun _ => x ^ (-(1 / 2) : ℝ)) (fun _ => dZ₀) dZ₀ hρ hDr.cutoff hΨc hx hCbp (fun _ => hy0)
    (fun b => (radialTerm_hasLocalSize hLaw hPow hρ hDr.cutoff hΨc hx1 b (hrim b) (fun _ => 0) rfl
      (κ := T.κ)).1)
    (fun b hb => (radialTerm_hasLocalSize hLaw hPow hρ hDr.cutoff hΨc hx1 b (hrim b) dZ₀ (by
      have h1 : enclosingCell b.1.1 = Y := (Finset.mem_filter.1 hb).2
      simp only [dZ₀, h1, hself]
      simp) (κ := T.κ)).2)
    (by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard hy0.le)
    (fun b => by
      rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right hcard (by positivity) |>.trans (le_of_eq (by ring)))
  have hC1 : ContDiffOn ℝ 1 G {η | ∀ b, ‖η b‖ < T.ballRadius} :=
    ContDiffOn.sum fun b _ =>
      (radialTerm_hasLocalSize hLaw hPow hρ hDr.cutoff hΨc hx1 b (hrim b) (fun _ => 0) rfl (κ := T.κ)).1
  have hobs : LocatedObservable T.ballRadius x T.κ r Ψ'
      (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) Cb
      (((4 * T.L ^ 4 : ℕ) : ℝ) * x ^ (-(1 / 2) : ℝ)) Y G :=
    ⟨hC1, hsize, by positivity, fun q => (hCbp q).le⟩
  have hres := cutoffTerm_expectation_bound hRim hDom hMean hEnds hExp T hρ hDr.cutoff hκ (Cq := Cb)
    (Cp := Cp (sizeParameters T))
    (fun q => (hCbp q).le) (fun q => (hCp _ q).le) (hA (parametersBeforeSide T)) (hT₀ _ _ _ hκ hlam) (by positivity)
    hst hrow hfin hsym htri Ψ' hd hz cb
    (fun V' hV' => (hXb t x F V' false hfl ⟨hLF, htt, n, hside, hn⟩ hV').1)
    (hRb t x f F V false hfl hrow ⟨hLF, htt, n, hside, hn⟩ hst.small_curvature) hLocT G hGd hGm hGρ hG0 hobs
  refine ⟨?_, hres.1, fun c X hX => (hres.2 c X hX).trans ?_⟩
  · have e : (fun η => Q.cutoffTerm Y η V * ballDensity Q.radialWeight (Q.exponent V) η) =
        fun η => ∑ b ∈ Sb, radialTerm T.p (η b) * ballDensity r Ψ' η := by
      funext η
      rw [hGd]
      show G η * ballDensity r (Q.exponent V) η = _
      rw [hd]
      simp only [G]
      rw [Finset.sum_mul]
    rw [e]
    exact integrable_finsetSum _ fun b _ => hbd b
  · have hE := (Real.exp_pos (-(T.κ / 2 ^ 5 * (bondSpan Y c : ℝ)))).le
    set Bv := 2 * (T₀ (4 * T.L ^ 4) T.κ T.chainParams.lam * (sizeConstantSum Cb 4 *
      (sizeConstantSum (Cp (sizeParameters T)) 4 * (1 + A (parametersBeforeSide T))) ^ 3)) with hBv
    calc Bv * (((4 * T.L ^ 4 : ℕ) : ℝ) * x ^ (-(1 / 2) : ℝ)) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) =
          (Bv * ((4 * T.L ^ 4 : ℕ) : ℝ)) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hy0.le) hE
end ResponseInTheExpansion
end YangMills.Construction
end
