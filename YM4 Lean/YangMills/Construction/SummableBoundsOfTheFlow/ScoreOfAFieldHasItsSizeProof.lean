import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import YangMills.Construction.SummableBoundsOfTheFlow.PowersOfACut
import YangMills.Construction.SummableBoundsOfTheFlow.RestAlongAFieldHasItsSizeProof
import YangMills.Construction.SummableBoundsOfTheFlow.ScoreOfAFieldHasItsSize
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped RealInnerProductSpace Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Estimates ConvexObservables MeasureTheory
namespace BondIntegration
namespace FieldScoreSize
section Radial
variable {ρ : ℝ} {p : ℝ → ℝ} {z : BondVector → BondVector}
def radialField (p : ℝ → ℝ) (z : BondVector → BondVector) (v : BondVector) : ℝ := radialCutoffSlope p v (z v)
theorem radialField_eq_zero_of_norm_lt (hpow : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector}
    (hv : ‖v‖ < 5 * ρ / 8) : radialField p z v = 0 := by
  by_cases h0 : v = 0
  · simp [radialField, radialCutoffSlope, h0]
  · have hu : 0 < ‖v‖ := norm_pos_iff.mpr h0
    obtain ⟨-, h2, -⟩ := hpow ρ p hρ hp
    have h3 := h2 _ hu hv 1 le_rfl
    rw [iteratedDeriv_one] at h3
    simp [radialField, radialCutoffSlope, h3]
theorem abs_radialField_le (v : BondVector) : |radialField p z v| ≤ |deriv p ‖v‖| * ‖z v‖ := by
  unfold radialField radialCutoffSlope
  by_cases h0 : v = 0
  · simp only [h0, inner_zero_left, mul_zero, abs_zero]
    positivity
  · have hu : 0 < ‖v‖ := norm_pos_iff.mpr h0
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hu)]
    have h1 := abs_real_inner_le_norm v (z v)
    calc |deriv p ‖v‖| * ‖v‖⁻¹ * |⟪v, z v⟫|
        ≤ |deriv p ‖v‖| * ‖v‖⁻¹ * (‖v‖ * ‖z v‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = |deriv p ‖v‖| * ‖z v‖ := by
          field_simp
theorem contDiffAt_deriv_of_isCutoff (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    ContDiffAt ℝ 1 (deriv p) u := by
  have hC : ContDiffAt ℝ 2 p u :=
    (hp.smooth.contDiffAt (Ico_mem_nhds h0 h1)).of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ _ from WithTop.coe_le_coe.mpr le_top)
  have h := hC.fderiv_right (m := 1) (by norm_num)
  have e : deriv p = fun y => fderiv ℝ p y 1 := rfl
  rw [e]
  exact h.clm_apply contDiffAt_const
theorem exists_hasFDerivAt_radialField (hp : IsCutoff ρ p) {v : BondVector} (h0 : v ≠ 0) (h1 : ‖v‖ < ρ) (hz : DifferentiableAt ℝ z v) :
    ∃ L : BondVector →L[ℝ] ℝ, HasFDerivAt (radialField p z) L v ∧
      ‖L‖ ≤ (|deriv (deriv p) ‖v‖| + 2 * |deriv p ‖v‖| * ‖v‖⁻¹) * ‖z v‖ + |deriv p ‖v‖| * ‖fderiv ℝ z v‖ := by
  have hu : 0 < ‖v‖ := norm_pos_iff.mpr h0
  have hdp := ((contDiffAt_deriv_of_isCutoff hp hu h1).differentiableAt (by norm_num)).hasDerivAt
  have hdn : DifferentiableAt ℝ (fun w : BondVector => ‖w‖) v :=
    (contDiffAt_norm ℝ (n := 1) h0).differentiableAt (by norm_num)
  set n : BondVector →L[ℝ] ℝ := fderiv ℝ (fun w : BondVector => ‖w‖) v with hn
  have hn1 : ‖n‖ = 1 := norm_fderiv_norm hdn
  have hnf : HasFDerivAt (fun w : BondVector => ‖w‖) n v := hdn.hasFDerivAt
  have ha : HasFDerivAt (fun w : BondVector => deriv p ‖w‖) (deriv (deriv p) ‖v‖ • n) v :=
    HasDerivAt.comp_hasFDerivAt v hdp hnf
  have hb : HasFDerivAt (fun w : BondVector => ‖w‖⁻¹) ((-(‖v‖ ^ 2)⁻¹) • n) v :=
    HasDerivAt.comp_hasFDerivAt v (hasDerivAt_inv hu.ne') hnf
  have hc : HasFDerivAt (fun w : BondVector => ⟪w, z w⟫) ((innerSL ℝ v).comp (fderiv ℝ z v) + innerSL ℝ (z v)) v := by
    have h := (hasFDerivAt_id v).inner ℝ hz.hasFDerivAt
    refine h.congr_fderiv ?_
    ext e
    simp [fderivInnerCLM_apply, real_inner_comm]
  have hm := (ha.mul hb).mul hc
  refine ⟨_, hm, ?_⟩
  set A := deriv p ‖v‖ with hA
  set B := deriv (deriv p) ‖v‖ with hB
  set u := ‖v‖ with hu'
  have hI : |⟪v, z v⟫| ≤ u * ‖z v‖ := abs_real_inner_le_norm v (z v)
  have t0 : ‖(innerSL ℝ v).comp (fderiv ℝ z v) + innerSL ℝ (z v)‖ ≤ u * ‖fderiv ℝ z v‖ + ‖z v‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [innerSL_apply_norm]
    · rw [innerSL_apply_norm]
  have t1 : ‖(A * u⁻¹) • ((innerSL ℝ v).comp (fderiv ℝ z v) + innerSL ℝ (z v))‖ ≤ |A| * u⁻¹ * (u * ‖fderiv ℝ z v‖ + ‖z v‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hu)]
    exact mul_le_mul_of_nonneg_left t0 (by positivity)
  have t2 : ‖A • ((-(u ^ 2)⁻¹) • n) + u⁻¹ • (B • n)‖ ≤ |A| * (u ^ 2)⁻¹ + u⁻¹ * |B| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_smul, norm_smul, hn1]
    simp only [Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hu), mul_one]
    rw [abs_of_pos (by positivity : 0 < (u ^ 2)⁻¹)]
  have e1 : ((fun w : BondVector => deriv p ‖w‖) * fun w : BondVector => ‖w‖⁻¹) v = A * u⁻¹ := rfl
  rw [e1]
  have t3 : ‖⟪v, z v⟫ • (A • ((-(u ^ 2)⁻¹) • n) + u⁻¹ • (B • n))‖ ≤
      (u * ‖z v‖) * (|A| * (u ^ 2)⁻¹ + u⁻¹ * |B|) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hI t2 (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ((add_le_add t1 t3).trans (le_of_eq ?_))
  field_simp
  ring
theorem contDiffAt_radialField (hpow : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector} (hv : ‖v‖ < ρ)
    (hz : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) z v) : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (radialField p z) v := by
  by_cases h1 : ‖v‖ < 5 * ρ / 8
  · have he : radialField p z =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      have hO : IsOpen {w : BondVector | ‖w‖ < 5 * ρ / 8} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hO.mem_nhds h1] with w hw
      exact radialField_eq_zero_of_norm_lt hpow hρ hp hw
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hu : 0 < ‖v‖ := lt_of_lt_of_le (by positivity) (not_lt.mp h1)
    have h0 : v ≠ 0 := norm_pos_iff.mp hu
    have hN : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun w : BondVector => ‖w‖) v := contDiffAt_norm ℝ h0
    have hD : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun w : BondVector => deriv p ‖w‖) v :=
      ContDiffAt.comp v (contDiffAt_deriv_of_isCutoff hp hu hv) hN
    have hI : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun w : BondVector => ‖w‖⁻¹) v := hN.inv hu.ne'
    have hC : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun w : BondVector => ⟪w, z w⟫) v := contDiffAt_id.inner ℝ hz
    exact (hD.mul hI).mul hC
def cutoffConstant (ρ : ℝ) : ℝ := 16 / (5 * ρ) + 1
theorem norm_fderiv_radialField_le (hpow : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector} {u : ℝ} (hv : ‖v‖ < ρ)
    (hz : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) z v) (hu0 : 0 ≤ u) (hzu : ‖z v‖ ≤ u) (hdu : ‖fderiv ℝ z v‖ ≤ u) :
    ‖fderiv ℝ (radialField p z) v‖ ≤ (|iteratedDeriv 2 p ‖v‖| + cutoffConstant ρ * |iteratedDeriv 1 p ‖v‖|) * u := by
  have hc : 0 < cutoffConstant ρ := by
    unfold cutoffConstant
    positivity
  by_cases h1 : ‖v‖ < 5 * ρ / 8
  · have he : radialField p z =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      have hO : IsOpen {w : BondVector | ‖w‖ < 5 * ρ / 8} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hO.mem_nhds h1] with w hw
      exact radialField_eq_zero_of_norm_lt hpow hρ hp hw
    rw [he.fderiv_eq]
    simp only [fderiv_fun_const, Pi.zero_apply, norm_zero]
    positivity
  · have hw : 0 < ‖v‖ := lt_of_lt_of_le (by positivity) (not_lt.mp h1)
    have h0 : v ≠ 0 := norm_pos_iff.mp hw
    obtain ⟨L, hL, hb⟩ := exists_hasFDerivAt_radialField hp h0 hv (hz.differentiableAt (by simp))
    rw [hL.fderiv]
    refine hb.trans ?_
    have e2 : iteratedDeriv 2 p ‖v‖ = deriv (deriv p) ‖v‖ := by
      simp [iteratedDeriv_succ]
    have e1 : iteratedDeriv 1 p ‖v‖ = deriv p ‖v‖ := by simp
    rw [e2, e1]
    have hinv : ‖v‖⁻¹ ≤ 8 / (5 * ρ) := by
      rw [inv_le_comm₀ hw (by positivity), inv_div]
      have := not_lt.mp h1
      linarith
    have h3 : 2 * |deriv p ‖v‖| * ‖v‖⁻¹ ≤ (16 / (5 * ρ)) * |deriv p ‖v‖| := by
      have h4 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 2 * |deriv p ‖v‖|)
      refine h4.trans (le_of_eq ?_)
      field_simp
      ring
    have hB := abs_nonneg (deriv (deriv p) ‖v‖)
    have hA := abs_nonneg (deriv p ‖v‖)
    have a1 : (|deriv (deriv p) ‖v‖| + 2 * |deriv p ‖v‖| * ‖v‖⁻¹) * ‖z v‖ ≤
        (|deriv (deriv p) ‖v‖| + (16 / (5 * ρ)) * |deriv p ‖v‖|) * u :=
      mul_le_mul (by linarith) hzu (norm_nonneg _) (by positivity)
    have a2 : |deriv p ‖v‖| * ‖fderiv ℝ z v‖ ≤ |deriv p ‖v‖| * u := mul_le_mul_of_nonneg_left hdu hA
    unfold cutoffConstant
    nlinarith
end Radial
section Moments
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem ballExpectation_mono {r : ℝ → ℝ} {Φ f g : BondField ι → ℝ}
    (hD : ∀ η, 0 ≤ ballDensity r Φ η) (hf : Integrable fun η => f η * ballDensity r Φ η)
    (hg : Integrable fun η => g η * ballDensity r Φ η)
    (hle : ∀ η, f η * ballDensity r Φ η ≤ g η * ballDensity r Φ η) :
    ballExpectation r Φ f ≤ ballExpectation r Φ g :=
  div_le_div_of_nonneg_right (integral_mono hf hg hle) (integral_nonneg hD)
theorem aestronglyMeasurable_mul_of_vanishing {U : Set (BondField ι)} (hU : IsOpen U) {f D : BondField ι → ℝ}
    (hf : ContinuousOn f U) (hD : AEStronglyMeasurable D volume) (h0 : ∀ η, η ∉ U → D η = 0) :
    AEStronglyMeasurable (fun η => f η * D η) volume := by
  have h1 : AEStronglyMeasurable (U.indicator f) volume :=
    (aestronglyMeasurable_indicator_iff hU.measurableSet).mpr
      (hf.aestronglyMeasurable hU.measurableSet)
  refine (h1.mul hD).congr (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : η ∈ U
  · simp [Set.indicator_of_mem hη]
  · simp [Set.indicator_of_notMem hη, h0 η hη]
theorem momentBound_of_le_add {r : ℝ → ℝ} {Φ f f₁ f₂ : BondField ι → ℝ} {U : Set (BondField ι)} (hU : IsOpen U)
    {q : ℕ} (hq : 1 ≤ q) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hD0 : ∀ η, 0 ≤ ballDensity r Φ η)
    (hDm : AEStronglyMeasurable (ballDensity r Φ) volume) (hDoff : ∀ η, η ∉ U → ballDensity r Φ η = 0)
    (hc : ContinuousOn f U) (hle : ∀ η ∈ U, |f η| ≤ |f₁ η| + |f₂ η|)
    (h1 : MomentBound r Φ f₁ q a) (h2 : MomentBound r Φ f₂ q b) :
    MomentBound r Φ f q (2 * (a + b)) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  set D := ballDensity r Φ with hDd
  let g : BondField ι → ℝ := fun η => 2 ^ m * (|f₁ η| ^ (m + 1) + |f₂ η| ^ (m + 1))
  have hgi : Integrable fun η => g η * D η := by
    have := (h1.1.add h2.1).const_mul ((2 : ℝ) ^ m)
    refine this.congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [Pi.add_apply, g]
    ring
  have hpt : ∀ η ∈ U, |f η| ^ (m + 1) ≤ g η := by
    intro η hη
    have h3 := add_pow_le (abs_nonneg (f₁ η)) (abs_nonneg (f₂ η)) (m + 1)
    rw [Nat.add_sub_cancel] at h3
    exact (pow_le_pow_left₀ (abs_nonneg _) (hle η hη) _).trans h3
  have hle2 : ∀ η, |f η| ^ (m + 1) * D η ≤ g η * D η := by
    intro η
    by_cases hη : η ∈ U
    · exact mul_le_mul_of_nonneg_right (hpt η hη) (hD0 η)
    · rw [hDoff η hη, mul_zero, mul_zero]
  have hfm : AEStronglyMeasurable (fun η => |f η| ^ (m + 1) * D η) volume :=
    aestronglyMeasurable_mul_of_vanishing hU (hc.abs.pow _) hDm hDoff
  have hfi : Integrable fun η => |f η| ^ (m + 1) * D η := by
    refine hgi.mono' hfm (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hD0 η))]
    exact hle2 η
  refine ⟨hfi, (ballExpectation_mono hD0 hfi hgi hle2).trans ?_⟩
  have hmean : ballExpectation r Φ g = 2 ^ m * (ballExpectation r Φ (fun η => |f₁ η| ^ (m + 1)) +
      ballExpectation r Φ (fun η => |f₂ η| ^ (m + 1))) := by
    unfold ballExpectation
    have e2 : ∫ η, g η * ballDensity r Φ η = 2 ^ m * ((∫ η, |f₁ η| ^ (m + 1) * ballDensity r Φ η) +
        ∫ η, |f₂ η| ^ (m + 1) * ballDensity r Φ η) := by
      rw [← integral_add h1.1 h2.1, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      simp only [g]
      ring
    rw [e2, mul_div_assoc, add_div]
  rw [hmean]
  have b1 := h1.2
  have b2 := h2.2
  have c1 : a ^ (m + 1) ≤ (a + b) ^ (m + 1) := pow_le_pow_left₀ ha (by linarith) _
  have c2 : b ^ (m + 1) ≤ (a + b) ^ (m + 1) := pow_le_pow_left₀ hb (by linarith) _
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  calc _ ≤ 2 ^ m * ((a + b) ^ (m + 1) + (a + b) ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) h2m
    _ = (2 * (a + b)) ^ (m + 1) := by
        rw [mul_pow, pow_succ 2 m]
        ring
theorem momentBound_mono {r : ℝ → ℝ} {Φ f : BondField ι → ℝ} {q : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : MomentBound r Φ f q a) : MomentBound r Φ f q b :=
  ⟨h.1, h.2.trans (pow_le_pow_left₀ ha hab _)⟩
theorem momentBound_cutoff_deriv {ρ x : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} (b : ι) (j q : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hj : 1 ≤ j) (hq : 1 ≤ q) (hD0 : ∀ η, 0 ≤ ballDensity (cutoffFactor ρ p) Ψ η)
    (hrim : ∀ (j q N : ℕ) (b' : ι), 1 ≤ j → 1 ≤ q →
      Integrable (fun η => |iteratedDeriv j p ‖η b'‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) ∧
      ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b'‖| ^ q) ≤ Cr j q N * (x ^ N)⁻¹) :
    MomentBound (cutoffFactor ρ p) Ψ (fun η => c * iteratedDeriv j p ‖η b‖) q (c * (1 + |Cr j q 0|)) := by
  obtain ⟨hi, hm⟩ := hrim j q 0 b hj hq
  have e1 : (fun η : BondField ι => |c * iteratedDeriv j p ‖η b‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) =
      fun η => c ^ q * (|iteratedDeriv j p ‖η b‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) := by
    funext η
    rw [abs_mul, abs_of_nonneg hc, mul_pow]
    ring
  refine ⟨by rw [e1]; exact hi.const_mul _, ?_⟩
  have e2 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => |c * iteratedDeriv j p ‖η b‖| ^ q) =
      c ^ q * ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) := by
    unfold ballExpectation
    rw [e1, integral_const_mul, mul_div_assoc]
  rw [e2, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simp only [pow_zero, inv_one, mul_one] at hm
  have h1 : Cr j q 0 ≤ 1 + |Cr j q 0| := by linarith [le_abs_self (Cr j q 0)]
  have h2 : 1 + |Cr j q 0| ≤ (1 + |Cr j q 0|) ^ q := le_self_pow₀ (by linarith [abs_nonneg (Cr j q 0)]) (by omega)
  linarith
end Moments
section Divergence
variable {z : BondVector → BondVector} {v : BondVector}
abbrev basisVector (i : Fin 3) : BondVector := EuclideanSpace.single i 1
theorem bondDivergence_eq : bondDivergence z = fun v => ∑ i : Fin 3, (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ) (fderiv ℝ z v (basisVector i)) := rfl
theorem contDiffAt_bondDivergence (hz : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) z v) : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (bondDivergence z) v := by
  have h1 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fderiv ℝ z) v := hz.fderiv_right (by norm_num)
  rw [bondDivergence_eq]
  refine ContDiffAt.sum fun i _ => ?_
  exact (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).contDiff.contDiffAt.comp v (h1.clm_apply contDiffAt_const)
theorem abs_proj_le_norm (i : Fin 3) (w : BondVector) : |(EuclideanSpace.proj i : BondVector →L[ℝ] ℝ) w| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  simpa using this
theorem abs_bondDivergence_le : |bondDivergence z v| ≤ 3 * ‖fderiv ℝ z v‖ := by
  have hs : ∀ i : Fin 3, |(EuclideanSpace.proj i : BondVector →L[ℝ] ℝ) (fderiv ℝ z v (basisVector i))| ≤ ‖fderiv ℝ z v‖ := by
    intro i
    refine (abs_proj_le_norm i _).trans ?_
    have := (fderiv ℝ z v).le_opNorm (basisVector i)
    simpa [basisVector] using this
  have e := congrFun (bondDivergence_eq (z := z)) v
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => hs i).trans ?_)
  simp
theorem abs_fderiv_bondDivergence_le {u : ℝ} (hz : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) z v)
    (hD : ∀ e e' : BondVector, ‖fderiv ℝ (fun v' => fderiv ℝ z v' e') v e‖ ≤ u * ‖e‖ * ‖e'‖) (e : BondVector) :
    |fderiv ℝ (bondDivergence z) v e| ≤ 3 * u * ‖e‖ := by
  have d1 : DifferentiableAt ℝ (fderiv ℝ z) v := (hz.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hd : ∀ i : Fin 3, HasFDerivAt (fun v' => (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ) (fderiv ℝ z v' (basisVector i)))
      ((EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).comp (fderiv ℝ (fun v' => fderiv ℝ z v' (basisVector i)) v)) v := fun i =>
    (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).hasFDerivAt.comp v
      (d1.clm_apply (differentiableAt_const (basisVector i))).hasFDerivAt
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hd i
  have e1 : fderiv ℝ (bondDivergence z) v = _ := hs.fderiv
  rw [e1]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  have hterm : ∀ i : Fin 3, |(EuclideanSpace.proj i : BondVector →L[ℝ] ℝ) (fderiv ℝ (fun v' => fderiv ℝ z v' (basisVector i)) v e)| ≤ u * ‖e‖ := by
    intro i
    refine (abs_proj_le_norm i _).trans ((hD e (basisVector i)).trans ?_)
    simp [basisVector]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => hterm i).trans ?_)
  simp
  linarith
end Divergence
section Along
variable {ι : Type} [Fintype ι] [DecidableEq ι] {H : BondField ι → ℝ} {U : BondVector → BondVector} {b : ι}
  {η : BondField ι}
theorem contDiffAt_fieldDerivative (hH : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) H η) (hU : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) U (η b)) :
    ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fieldDerivative b U H) η := by apply _root_.YangMills.Construction.IteratedDerivative.MovingFieldRemainderSize.fieldDerivative_contDiffAt <;> assumption
theorem fderiv_fieldDerivative_apply (hH : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) H η) (hU : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) U (η b))
    (u : BondField ι) :
    fderiv ℝ (fieldDerivative b U H) η u = (fderiv ℝ (fderiv ℝ H) η u) (bondVariation b (U (η b))) +
      fderiv ℝ H η (bondVariation b (fderiv ℝ U (η b) (u b))) := by apply _root_.YangMills.Construction.IteratedDerivative.MovingFieldRemainderSize.fderiv_fieldDerivative <;> assumption
theorem fderiv_comp_eval_apply {f : BondVector → ℝ} (hf : DifferentiableAt ℝ f (η b)) (u : BondField ι) :
    fderiv ℝ (fun ζ : BondField ι => f (ζ b)) η u = fderiv ℝ f (η b) (u b) := by
  have h := (HasFDerivAt.comp (g := f) (f := fun ζ : BondField ι => ζ b) η hf.hasFDerivAt
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ fun ζ : BondField ι => ζ b) η u = _
  rw [h]
  rfl
theorem fderiv_fderiv_apply_eq_secondDerivAlong {Ψ : BondField ι → ℝ} (hΨ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Ψ η) (u v : BondField ι) :
    (fderiv ℝ (fderiv ℝ Ψ) η v) u = secondDerivAlong Ψ η u v := by
  have d1 : DifferentiableAt ℝ (fderiv ℝ Ψ) η := (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have h := (d1.hasFDerivAt.clm_apply (hasFDerivAt_const u η)).fderiv
  unfold secondDerivAlong
  rw [h]
  simp
end Along
end FieldScoreSize
open FieldScoreSize in
set_option maxHeartbeats 1600000 in
theorem fieldScoreSizeStatement_holds (hSz : localSizeOfQuadraticBoundsStatement) (hpow : cutoffDerivBoundsStatement)
    (hLaw : normalizedBallLawIsProbabilityStatement) : fieldScoreSizeStatement := by
  classical
  intro ρ p Cr lam W W₀ hρ hp hlam hW hW₀
  set c : ℝ := cutoffConstant ρ with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ 16 / (5 * ρ) := by positivity
    simp only [hc, cutoffConstant]
    linarith
  set C₂ : ℕ → ℝ := fun q => 2 * ((1 + |Cr 2 q 0|) + c * (1 + |Cr 1 q 0|)) with hC₂
  have hC₂0 : ∀ q, 0 ≤ C₂ q := fun q => by
    simp only [hC₂]
    positivity
  have hM0 : ∀ q, 0 ≤ lpMomentConstant lam W₀ W q := fun q => by
    unfold lpMomentConstant
    have : 0 ≤ ∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W) := Finset.prod_nonneg fun k _ => by positivity
    positivity
  refine ⟨fun q => 2 * (lpMomentConstant lam W₀ W q + C₂ q), fun q => by
    have := hM0 q
    have := hC₂0 q
    positivity, ?_⟩
  intro ι _ _ x κ C A u d Ψ b w z hx hκ hA hu hd hΨ hconv hWd hrim hw hWw hP1 hP2 hz
  have hx0 : 0 < x := by linarith
  set r := Real.sqrt x with hr
  have hr1 : 1 ≤ r := by
    rw [hr, Real.one_le_sqrt]
    exact hx
  have hrr : r * r = x := Real.mul_self_sqrt hx0.le
  have hrx : r ≤ x := by nlinarith
  set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_apply b).norm continuous_const
  obtain ⟨-, -, -, -, hDmeas, hD0, -, -, -, hDne, -⟩ := hLaw ι ρ p Ψ hρ hp hΨ.continuous
  have hDoff : ∀ η, η ∉ U → ballDensity (cutoffFactor ρ p) Ψ η = 0 := fun η hη => by
    by_contra h
    exact hη ((hDne η).1 h)
  have hDm : AEStronglyMeasurable (ballDensity (cutoffFactor ρ p) Ψ) volume := hDmeas.aestronglyMeasurable
  have hΨ2 : ∀ η, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Ψ η := fun η => (hΨ.of_le (by norm_num)).contDiffAt
  have hz1 : ∀ v : BondVector, ‖v‖ < ρ → ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) z v := fun v hv =>
    (hz v hv).1.of_le (by norm_num)
  set T₁ : BondField ι → ℝ := fieldDerivative b z Ψ with hT₁
  set T₃ : BondField ι → ℝ := fun η => bondDivergence z (η b) with hT₃
  set T₂ : BondField ι → ℝ := fun η => radialField p z (η b) with hT₂
  set H₁ : BondField ι → ℝ := fun η => T₁ η - T₃ η with hH₁
  have hS : fieldScore p Ψ b z = fun η => H₁ η + T₂ η := by
    funext η
    simp only [fieldScore, hH₁, hT₁, hT₃, hT₂, fieldDerivative, radialField]
    ring
  have hpr : ∀ η : BondField ι, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun ζ : BondField ι => ζ b) η := fun η =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).contDiff.contDiffAt
  have sT₁ : ∀ η ∈ U, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) T₁ η := fun η hη => contDiffAt_fieldDerivative (hΨ2 η) (hz1 _ (hη b))
  have sT₃ : ∀ η ∈ U, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) T₃ η := fun η hη =>
    ContDiffAt.comp (g := bondDivergence z) (f := fun ζ : BondField ι => ζ b) η (contDiffAt_bondDivergence (hz _ (hη b)).1) (hpr η)
  have sT₂ : ∀ η ∈ U, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) T₂ η := fun η hη =>
    ContDiffAt.comp (g := radialField p z) (f := fun ζ : BondField ι => ζ b) η
      (contDiffAt_radialField hpow hρ hp (hη b) (hz1 _ (hη b))) (hpr η)
  have sH₁ : ∀ η ∈ U, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) H₁ η := fun η hη => (sT₁ η hη).sub (sT₃ η hη)
  have sS : ∀ η ∈ U, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun η => H₁ η + T₂ η) η := fun η hη =>
    (sH₁ η hη).add (sT₂ η hη)
  have onS : ContDiffOn ℝ 1 (fun η => H₁ η + T₂ η) U := fun η hη => (sS η hη).contDiffWithinAt
  have onT₂ : ContDiffOn ℝ 1 T₂ U := fun η hη => (sT₂ η hη).contDiffWithinAt
  set Mη : BondField ι → ℝ := fun η => x * ∑ b', w b' * ‖η b'‖ ^ 2 + 1 with hMη
  have hM1 : ∀ η, 1 ≤ Mη η := fun η => by
    have : 0 ≤ ∑ b', w b' * ‖η b'‖ ^ 2 := Finset.sum_nonneg fun b' _ => mul_nonneg (hw b') (sq_nonneg _)
    simp only [hMη]
    nlinarith
  set h₁ : ℝ := (2 * A + 3) * r * u with hh₁
  have hh₁0 : 0 ≤ h₁ := by positivity
  have hv : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H₁ η - 0| ≤ h₁ * Mη η := by
    intro η hη
    obtain ⟨-, hzv, hdz, -⟩ := hz _ (hη b)
    have a1 : |T₁ η| ≤ A * r * Mη η * u := by
      have := hP1 η (z (η b)) hη
      refine this.trans (mul_le_mul_of_nonneg_left hzv ?_)
      have := hM1 η
      positivity
    have a2 : |T₃ η| ≤ 3 * u := abs_bondDivergence_le.trans (by linarith)
    have hM := hM1 η
    have a3 : 3 * u ≤ 3 * r * Mη η * u := by
      have h1 : 1 ≤ r * Mη η := by nlinarith
      nlinarith
    rw [sub_zero]
    calc |H₁ η| ≤ |T₁ η| + |T₃ η| := abs_sub _ _
      _ ≤ A * r * Mη η * u + 3 * r * Mη η * u := add_le_add a1 (a2.trans a3)
      _ ≤ h₁ * Mη η := by
          simp only [hh₁]
          have : 0 ≤ A * r * Mη η * u := by positivity
          nlinarith
  have hg : ∀ (η : BondField ι) (b' : ι), (∀ b, ‖η b‖ < ρ) →
      bondGradNorm H₁ b' η ≤ r * h₁ * Real.exp (-(2 * κ * d b' b)) * Mη η := by
    intro η b' hη
    obtain ⟨hz2, hzv, hdz, hdd⟩ := hz _ (hη b)
    have hE0 := Real.exp_pos (-(2 * κ * d b' b))
    have hM := hM1 η
    have hB : 0 ≤ r * h₁ * Real.exp (-(2 * κ * d b' b)) * Mη η := by positivity
    unfold bondGradNorm
    refine ContinuousLinearMap.opNorm_le_of_unit_norm hB fun e' he' => ?_
    have e0 : ((fderiv ℝ H₁ η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b')) e' = fderiv ℝ H₁ η (bondVariation b' e') := rfl
    rw [e0, Real.norm_eq_abs]
    have dT₁ : DifferentiableAt ℝ T₁ η := (sT₁ η hη).differentiableAt (by simp)
    have dT₃ : DifferentiableAt ℝ T₃ η := (sT₃ η hη).differentiableAt (by simp)
    have hdiv : DifferentiableAt ℝ (bondDivergence z) (η b) := (contDiffAt_bondDivergence hz2).differentiableAt (by simp)
    have eH : fderiv ℝ H₁ η (bondVariation b' e') = fderiv ℝ T₁ η (bondVariation b' e') - fderiv ℝ T₃ η (bondVariation b' e') := by
      have := (dT₁.hasFDerivAt.sub dT₃.hasFDerivAt).fderiv
      change fderiv ℝ (T₁ - T₃) η (bondVariation b' e') = _
      rw [this]
      rfl
    rw [eH, hT₁, fderiv_fieldDerivative_apply (hΨ2 η) (hz1 _ (hη b)), fderiv_comp_eval_apply hdiv, fderiv_fderiv_apply_eq_secondDerivAlong (hΨ2 η)]
    have t1 : |secondDerivAlong Ψ η (bondVariation b (z (η b))) (bondVariation b' e')| ≤ A * x * Real.exp (-(2 * κ * d b' b)) * u := by
      have := hP2 η b' (z (η b)) e' hη
      rw [he', mul_one] at this
      exact this.trans (mul_le_mul_of_nonneg_left hzv (by positivity))
    have hsq : r * h₁ = (2 * A + 3) * x * u := by
      simp only [hh₁]
      rw [← hrr]
      ring
    rw [hsq]
    by_cases hb : b' = b
    · have e1 : (bondVariation b' e' : BondField ι) b = e' := by
        rw [hb]
        simp [bondVariation]
      have e2 : Real.exp (-(2 * κ * d b' b)) = 1 := by
        rw [hb, hd.self]
        simp
      rw [e1]
      rw [e2] at t1 ⊢
      have t2 : |fderiv ℝ Ψ η (bondVariation b (fderiv ℝ z (η b) e'))| ≤ A * r * Mη η * u := by
        have h1 := hP1 η (fderiv ℝ z (η b) e') hη
        have h2 : ‖fderiv ℝ z (η b) e'‖ ≤ u := by
          have := (fderiv ℝ z (η b)).le_opNorm e'
          rw [he', mul_one] at this
          exact this.trans hdz
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      have t3 : |fderiv ℝ (bondDivergence z) (η b) e'| ≤ 3 * u := by
        have := abs_fderiv_bondDivergence_le hz2 hdd e'
        rwa [he', mul_one] at this
      have hAx : 0 ≤ A * x * u := by positivity
      have b1 : A * x * 1 * u ≤ A * x * u * Mη η := by nlinarith
      have b2 : A * r * Mη η * u ≤ A * x * u * Mη η := by
        have : A * u * Mη η * r ≤ A * u * Mη η * x := mul_le_mul_of_nonneg_left hrx (by positivity)
        nlinarith
      have b3 : 3 * u ≤ 3 * x * u * Mη η := by
        have h1 : 1 ≤ x * Mη η := by nlinarith
        nlinarith
      calc _ ≤ |secondDerivAlong Ψ η (bondVariation b (z (η b))) (bondVariation b' e')| + |fderiv ℝ Ψ η (bondVariation b (fderiv ℝ z (η b) e'))| +
            |fderiv ℝ (bondDivergence z) (η b) e'| := (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
        _ ≤ _ := by nlinarith
    · have e1 : (bondVariation b' e' : BondField ι) b = 0 := Pi.single_eq_of_ne (Ne.symm hb) _
      rw [e1]
      simp only [map_zero, sub_zero]
      have e3 : (bondVariation b (0 : BondVector) : BondField ι) = 0 := by simp [bondVariation]
      rw [e3, map_zero, add_zero]
      refine t1.trans ?_
      have : 0 ≤ x * u * Real.exp (-(2 * κ * d b' b)) := by positivity
      have b1 : A * x * Real.exp (-(2 * κ * d b' b)) * u ≤ (2 * A + 3) * x * u * Real.exp (-(2 * κ * d b' b)) := by nlinarith
      have b2 : (2 * A + 3) * x * u * Real.exp (-(2 * κ * d b' b)) ≤ (2 * A + 3) * x * u * Real.exp (-(2 * κ * d b' b)) * Mη η :=
        le_mul_of_one_le_right (by positivity) hM
      exact b1.trans b2
  have s₁ := hSz ι ρ x lam κ W W₀ C h₁ 0 d Ψ p (fun b' => d b' b) w H₁ hρ hx hlam hκ hW hW₀ hh₁0 hp hd hconv hWd hw hWw
    (fun η hη => sH₁ η hη) hv hg
  obtain ⟨dif₁, H₀₁, hm₁⟩ := s₁
  have zeroMoment : ∀ q : ℕ, 1 ≤ q → MomentBound (cutoffFactor ρ p) Ψ (fun _ : BondField ι => (0 : ℝ)) q 0 := by
    intro q hq
    have hq0 : q ≠ 0 := by omega
    refine ⟨by simp [hq0], ?_⟩
    unfold ballExpectation
    simp [hq0]
  have hm₂ : ∀ q : ℕ, 1 ≤ q → MomentBound (cutoffFactor ρ p) Ψ (fun η => T₂ η - 0) q (C₂ q * u) ∧
      ∀ b' : ι, MomentBound (cutoffFactor ρ p) Ψ (bondGradNorm T₂ b') q
        (C₂ q * r * u * Real.exp (-(2 * κ * d b' b))) := by
    intro q hq
    have m₁ := momentBound_cutoff_deriv (Cr := Cr) b 2 q u hu (by norm_num) hq hD0 hrim
    have m₂ := momentBound_cutoff_deriv (Cr := Cr) b 1 q (u * c) (by positivity) le_rfl hq hD0 hrim
    have hCu : 2 * (u * (1 + |Cr 2 q 0|) + u * c * (1 + |Cr 1 q 0|)) = C₂ q * u := by
      simp only [hC₂]
      ring
    have a₂0 : 0 ≤ u * (1 + |Cr 2 q 0|) := by positivity
    have a₁0 : 0 ≤ u * c * (1 + |Cr 1 q 0|) := by positivity
    have hdT : ∀ η ∈ U, ∀ (b' : ι) (e : BondVector), fderiv ℝ T₂ η (bondVariation b' e) =
        fderiv ℝ (radialField p z) (η b) ((bondVariation b' e : BondField ι) b) := fun η hη b' e =>
      fderiv_comp_eval_apply ((contDiffAt_radialField hpow hρ hp (hη b) (hz1 _ (hη b))).differentiableAt (by simp)) _
    have hcontP : ∀ b' : ι, ContinuousOn (bondGradNorm T₂ b') U := fun b' => by
      have hf : ContinuousOn (fderiv ℝ T₂) U := onT₂.continuousOn_fderiv_of_isOpen hUo le_rfl
      exact (hf.clm_comp continuousOn_const).norm
    refine ⟨?_, fun b' => ?_⟩
    · have := momentBound_of_le_add hUo hq a₂0 a₁0 hD0 hDm hDoff (f := fun η => T₂ η - 0)
        ((onT₂.continuousOn).sub continuousOn_const) (fun η hη => ?_) m₁ m₂
      · rw [hCu] at this
        exact this
      · rw [sub_zero]
        obtain ⟨-, hzv, -, -⟩ := hz _ (hη b)
        have h1 := abs_radialField_le (p := p) (z := z) (η b)
        have h2 : |deriv p ‖η b‖| * ‖z (η b)‖ ≤ |deriv p ‖η b‖| * u := mul_le_mul_of_nonneg_left hzv (abs_nonneg _)
        have h3 : |u * c * iteratedDeriv 1 p ‖η b‖| = u * c * |deriv p ‖η b‖| := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ u * c), iteratedDeriv_one]
        have h4 : |deriv p ‖η b‖| * u ≤ u * c * |deriv p ‖η b‖| := by
          have := abs_nonneg (deriv p ‖η b‖)
          nlinarith [mul_nonneg hu this]
        rw [h3]
        have h5 := abs_nonneg (u * iteratedDeriv 2 p ‖η b‖)
        change |radialField p z (η b)| ≤ _
        linarith
    · by_cases hb : b' = b
      · have e2 : Real.exp (-(2 * κ * d b' b)) = 1 := by
          rw [hb, hd.self]
          simp
        have := momentBound_of_le_add hUo hq a₂0 a₁0 hD0 hDm hDoff (f := bondGradNorm T₂ b') (hcontP b') (fun η hη => ?_) m₁ m₂
        · rw [hCu] at this
          rw [e2, mul_one]
          refine momentBound_mono (by have := hC₂0 q; positivity) ?_ this
          have h0 : 0 ≤ C₂ q * u := mul_nonneg (hC₂0 q) hu
          have e3 : C₂ q * r * u = C₂ q * u * r := by ring
          rw [e3]
          exact le_mul_of_one_le_right h0 hr1
        · obtain ⟨-, hzv, hdz, -⟩ := hz _ (hη b)
          have h0 : 0 ≤ bondGradNorm T₂ b' η := norm_nonneg _
          rw [abs_of_nonneg h0]
          have h1 := norm_fderiv_radialField_le hpow hρ hp (hη b) (hz1 _ (hη b)) hu hzv hdz
          have h2 : bondGradNorm T₂ b' η ≤ ‖fderiv ℝ (radialField p z) (η b)‖ := by
            unfold bondGradNorm
            refine ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun e he => ?_
            have e0 : ((fderiv ℝ T₂ η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b')) e = fderiv ℝ T₂ η (bondVariation b' e) := rfl
            rw [e0, hdT η hη b' e]
            have e1 : (bondVariation b' e : BondField ι) b = e := by
              rw [hb]
              simp [bondVariation]
            rw [e1]
            have := (fderiv ℝ (radialField p z) (η b)).le_opNorm e
            rwa [he, mul_one] at this
          refine h2.trans (h1.trans (le_of_eq ?_))
          rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg (by positivity : 0 ≤ u * c)]
          ring
      · have hzero : ∀ η ∈ U, bondGradNorm T₂ b' η = 0 := by
          intro η hη
          refine le_antisymm ?_ (norm_nonneg _)
          unfold bondGradNorm
          refine ContinuousLinearMap.opNorm_le_of_unit_norm le_rfl fun e he => ?_
          have e0 : ((fderiv ℝ T₂ η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b')) e = fderiv ℝ T₂ η (bondVariation b' e) := rfl
          rw [e0, hdT η hη b' e]
          have e1 : (bondVariation b' e : BondField ι) b = 0 := Pi.single_eq_of_ne (Ne.symm hb) _
          rw [e1]
          simp
        have := momentBound_of_le_add hUo hq le_rfl le_rfl hD0 hDm hDoff (f := bondGradNorm T₂ b') (hcontP b')
          (fun η hη => by rw [hzero η hη]; simp) (zeroMoment q hq) (zeroMoment q hq)
        refine momentBound_mono (by simp) ?_ this
        have := hC₂0 q
        have := Real.exp_pos (-(2 * κ * d b' b))
        simp only [add_zero, mul_zero]
        positivity
  rw [hS]
  have hcontS : ∀ b' : ι, ContinuousOn (bondGradNorm (fun η => H₁ η + T₂ η) b') U := fun b' => by
    have hf : ContinuousOn (fderiv ℝ (fun η => H₁ η + T₂ η)) U := onS.continuousOn_fderiv_of_isOpen hUo le_rfl
    exact (hf.clm_comp continuousOn_const).norm
  set hf : ℝ := (2 * A + 4) * r * u with hhf
  have hf₁ : h₁ ≤ hf := by
    simp only [hh₁, hhf]
    have : 0 ≤ r * u := by positivity
    nlinarith
  have hfu : u ≤ hf := by
    simp only [hhf]
    have : 0 ≤ A * r * u := by positivity
    nlinarith
  refine ⟨fun η hη => sS η hη |>.contDiffWithinAt, fun η hη => (sS η hη).differentiableAt (by simp), H₀₁, fun q hq => ⟨?_, fun b' => ?_⟩⟩
  · have hMq := hM0 q
    have hCq := hC₂0 q
    have a0 : 0 ≤ lpMomentConstant lam W₀ W q * h₁ := by positivity
    have b0 : 0 ≤ C₂ q * u := by positivity
    have := momentBound_of_le_add hUo hq a0 b0 hD0 hDm hDoff (f := fun η => H₁ η + T₂ η - H₀₁)
      ((onS.continuousOn).sub continuousOn_const) (fun η hη => ?_) (hm₁ q hq).1 (hm₂ q hq).1
    · refine momentBound_mono (by positivity) ?_ this
      have c1 : lpMomentConstant lam W₀ W q * h₁ ≤ lpMomentConstant lam W₀ W q * hf := mul_le_mul_of_nonneg_left hf₁ hMq
      have c2 : C₂ q * u ≤ C₂ q * hf := mul_le_mul_of_nonneg_left hfu hCq
      nlinarith
    · have : H₁ η + T₂ η - H₀₁ = (H₁ η - H₀₁) + (T₂ η - 0) := by ring
      rw [this]
      exact abs_add_le _ _
  · have hMq := hM0 q
    have hCq := hC₂0 q
    have hE0 := Real.exp_pos (-(2 * κ * d b' b))
    have a0 : 0 ≤ lpMomentConstant lam W₀ W q * r * h₁ * Real.exp (-(2 * κ * d b' b)) := by positivity
    have b0 : 0 ≤ C₂ q * r * u * Real.exp (-(2 * κ * d b' b)) := by positivity
    have := momentBound_of_le_add hUo hq a0 b0 hD0 hDm hDoff (f := bondGradNorm (fun η => H₁ η + T₂ η) b') (hcontS b')
      (fun η hη => ?_) ((hm₁ q hq).2 b') ((hm₂ q hq).2 b')
    · refine momentBound_mono (by positivity) ?_ this
      have hrE : 0 ≤ r * Real.exp (-(2 * κ * d b' b)) := by positivity
      have c1 : lpMomentConstant lam W₀ W q * r * h₁ * Real.exp (-(2 * κ * d b' b)) ≤
          lpMomentConstant lam W₀ W q * r * hf * Real.exp (-(2 * κ * d b' b)) := by
        have := mul_le_mul_of_nonneg_left hf₁ (mul_nonneg hMq hrE)
        nlinarith
      have c2 : C₂ q * r * u * Real.exp (-(2 * κ * d b' b)) ≤ C₂ q * r * hf * Real.exp (-(2 * κ * d b' b)) := by
        have := mul_le_mul_of_nonneg_left hfu (mul_nonneg hCq hrE)
        nlinarith
      have e : 2 * (lpMomentConstant lam W₀ W q + C₂ q) * r * hf * Real.exp (-(2 * κ * d b' b)) =
          2 * (lpMomentConstant lam W₀ W q * r * hf * Real.exp (-(2 * κ * d b' b)) +
            C₂ q * r * hf * Real.exp (-(2 * κ * d b' b))) := by ring
      rw [e]
      linarith
    · have d1 : DifferentiableAt ℝ H₁ η := (sH₁ η hη).differentiableAt (by simp)
      have d2 : DifferentiableAt ℝ T₂ η := (sT₂ η hη).differentiableAt (by simp)
      have e1 : fderiv ℝ (fun η => H₁ η + T₂ η) η = fderiv ℝ H₁ η + fderiv ℝ T₂ η :=
        (d1.hasFDerivAt.add d2.hasFDerivAt).fderiv
      have h0 : 0 ≤ bondGradNorm (fun η => H₁ η + T₂ η) b' η := norm_nonneg _
      have h1 : 0 ≤ bondGradNorm H₁ b' η := norm_nonneg _
      have h2 : 0 ≤ bondGradNorm T₂ b' η := norm_nonneg _
      rw [abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonneg h2]
      unfold bondGradNorm
      rw [e1, ContinuousLinearMap.add_comp]
      exact norm_add_le _ _
end BondIntegration
end YangMills.Construction
end
