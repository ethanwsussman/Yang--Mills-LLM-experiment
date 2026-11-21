import YangMills.Construction.SummableBoundsOfTheFlow.ScoreOfAFieldHasItsSizeProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeOfACutHasItsSize
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped RealInnerProductSpace Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames MeasureTheory
namespace YangMills.Construction.Estimates
namespace CutoffSlope
def bondCutoffSlope (p : ℝ → ℝ) (e v : BondVector) : ℝ := deriv p ‖v‖ * ‖v‖⁻¹ * ⟪v, e⟫
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem bondCutoffSlope_eq_zero_of_norm_lt (hpow : cutoffDerivBoundsStatement) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (e : BondVector) {v : BondVector} (hv : ‖v‖ < 5 * ρ / 8) :
    bondCutoffSlope p e v = 0 := by
  by_cases h0 : v = 0
  · simp [bondCutoffSlope, h0]
  · have hu : 0 < ‖v‖ := norm_pos_iff.mpr h0
    obtain ⟨-, h2, -⟩ := hpow ρ p hρ hp
    have h3 := h2 _ hu hv 1 le_rfl
    rw [iteratedDeriv_one] at h3
    simp [bondCutoffSlope, h3]
theorem abs_bondCutoffSlope_le (e v : BondVector) :
    |bondCutoffSlope p e v| ≤ |deriv p ‖v‖| * ‖e‖ := by
  unfold bondCutoffSlope
  by_cases h0 : v = 0
  · simp only [h0, inner_zero_left, mul_zero, abs_zero]
    positivity
  · have hu : 0 < ‖v‖ := norm_pos_iff.mpr h0
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hu)]
    have h1 := abs_real_inner_le_norm v e
    calc |deriv p ‖v‖| * ‖v‖⁻¹ * |⟪v, e⟫|
        ≤ |deriv p ‖v‖| * ‖v‖⁻¹ * (‖v‖ * ‖e‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = |deriv p ‖v‖| * ‖e‖ := by
          field_simp
theorem contDiffAt_deriv_cutoff (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    ContDiffAt ℝ 1 (deriv p) u := by apply _root_.YangMills.Construction.BondIntegration.FieldScoreSize.contDiffAt_deriv_of_isCutoff <;> assumption
theorem exists_hasFDerivAt_bondCutoffSlope (hp : IsCutoff ρ p) {e v : BondVector} (h0 : v ≠ 0)
    (h1 : ‖v‖ < ρ) :
    ∃ L : BondVector →L[ℝ] ℝ, HasFDerivAt (bondCutoffSlope p e) L v ∧
      ‖L‖ ≤ (|deriv (deriv p) ‖v‖| + 2 * |deriv p ‖v‖| * ‖v‖⁻¹) * ‖e‖ := by
  have hu : 0 < ‖v‖ := norm_pos_iff.mpr h0
  have hdp := ((contDiffAt_deriv_cutoff hp hu h1).differentiableAt (by norm_num)).hasDerivAt
  have hdn : DifferentiableAt ℝ (fun w : BondVector => ‖w‖) v :=
    (contDiffAt_norm ℝ (n := 1) h0).differentiableAt (by norm_num)
  set n : BondVector →L[ℝ] ℝ := fderiv ℝ (fun w : BondVector => ‖w‖) v with hn
  have hn1 : ‖n‖ = 1 := norm_fderiv_norm hdn
  have hnf : HasFDerivAt (fun w : BondVector => ‖w‖) n v := hdn.hasFDerivAt
  have ha : HasFDerivAt (fun w : BondVector => deriv p ‖w‖) (deriv (deriv p) ‖v‖ • n) v :=
    HasDerivAt.comp_hasFDerivAt v hdp hnf
  have hb : HasFDerivAt (fun w : BondVector => ‖w‖⁻¹) ((-(‖v‖ ^ 2)⁻¹) • n) v :=
    HasDerivAt.comp_hasFDerivAt v (hasDerivAt_inv hu.ne') hnf
  have hc : HasFDerivAt (fun w : BondVector => ⟪w, e⟫) (innerSL ℝ e) v := by
    have h : (fun w : BondVector => ⟪w, e⟫) = fun w => innerSL ℝ e w := by
      funext w
      simp [real_inner_comm]
    rw [h]
    exact (innerSL ℝ e).hasFDerivAt
  have hm := (ha.mul hb).mul hc
  refine ⟨_, hm, ?_⟩
  set A := deriv p ‖v‖ with hA
  set B := deriv (deriv p) ‖v‖ with hB
  set u := ‖v‖ with hu'
  have hI : |⟪v, e⟫| ≤ u * ‖e‖ := abs_real_inner_le_norm v e
  have t1 : ‖(A * u⁻¹) • innerSL ℝ e‖ ≤ |A| * u⁻¹ * ‖e‖ := by
    rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hu)]
  have t2 : ‖A • ((-(u ^ 2)⁻¹) • n) + u⁻¹ • (B • n)‖ ≤ |A| * (u ^ 2)⁻¹ + u⁻¹ * |B| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_smul, norm_smul, hn1]
    simp only [Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hu), mul_one]
    rw [abs_of_pos (by positivity : 0 < (u ^ 2)⁻¹)]
  have e1 : ((fun w : BondVector => deriv p ‖w‖) * fun w : BondVector => ‖w‖⁻¹) v = A * u⁻¹ := rfl
  rw [e1]
  have t3 : ‖⟪v, e⟫ • (A • ((-(u ^ 2)⁻¹) • n) + u⁻¹ • (B • n))‖ ≤
      (u * ‖e‖) * (|A| * (u ^ 2)⁻¹ + u⁻¹ * |B|) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hI t2 (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ((add_le_add t1 t3).trans (le_of_eq ?_))
  field_simp
  ring
theorem contDiffAt_bondCutoffSlope (hpow : cutoffDerivBoundsStatement) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (e : BondVector) {v : BondVector} (hv : ‖v‖ < ρ) :
    ContDiffAt ℝ 1 (bondCutoffSlope p e) v := by
  by_cases h1 : ‖v‖ < 5 * ρ / 8
  · have he : bondCutoffSlope p e =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      have hO : IsOpen {w : BondVector | ‖w‖ < 5 * ρ / 8} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hO.mem_nhds h1] with w hw
      exact bondCutoffSlope_eq_zero_of_norm_lt hpow hρ hp e hw
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hu : 0 < ‖v‖ := lt_of_lt_of_le (by positivity) (not_lt.mp h1)
    have h0 : v ≠ 0 := norm_pos_iff.mp hu
    have hN : ContDiffAt ℝ 1 (fun w : BondVector => ‖w‖) v := contDiffAt_norm ℝ h0
    have hD : ContDiffAt ℝ 1 (fun w : BondVector => deriv p ‖w‖) v :=
      ContDiffAt.comp v (contDiffAt_deriv_cutoff hp hu hv) hN
    have hI : ContDiffAt ℝ 1 (fun w : BondVector => ‖w‖⁻¹) v := hN.inv hu.ne'
    have hC : ContDiffAt ℝ 1 (fun w : BondVector => ⟪w, e⟫) v := contDiffAt_id.inner ℝ contDiffAt_const
    exact (hD.mul hI).mul hC
def cutoffConstant (ρ : ℝ) : ℝ := 16 / (5 * ρ)
theorem norm_fderiv_bondCutoffSlope_le (hpow : cutoffDerivBoundsStatement) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (e : BondVector) {v : BondVector} (hv : ‖v‖ < ρ) :
    ‖fderiv ℝ (bondCutoffSlope p e) v‖ ≤
      (|iteratedDeriv 2 p ‖v‖| + cutoffConstant ρ * |iteratedDeriv 1 p ‖v‖|) * ‖e‖ := by
  have hc : 0 < cutoffConstant ρ := by
    unfold cutoffConstant
    positivity
  by_cases h1 : ‖v‖ < 5 * ρ / 8
  · have he : bondCutoffSlope p e =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      have hO : IsOpen {w : BondVector | ‖w‖ < 5 * ρ / 8} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hO.mem_nhds h1] with w hw
      exact bondCutoffSlope_eq_zero_of_norm_lt hpow hρ hp e hw
    rw [he.fderiv_eq]
    simp only [fderiv_fun_const, Pi.zero_apply, norm_zero]
    positivity
  · have hu : 0 < ‖v‖ := lt_of_lt_of_le (by positivity) (not_lt.mp h1)
    have h0 : v ≠ 0 := norm_pos_iff.mp hu
    obtain ⟨L, hL, hb⟩ := exists_hasFDerivAt_bondCutoffSlope (e := e) hp h0 hv
    rw [hL.fderiv]
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have e2 : iteratedDeriv 2 p ‖v‖ = deriv (deriv p) ‖v‖ := by
      simp [iteratedDeriv_succ]
    have e1 : iteratedDeriv 1 p ‖v‖ = deriv p ‖v‖ := by simp
    rw [e2, e1]
    have hinv : ‖v‖⁻¹ ≤ 8 / (5 * ρ) := by
      rw [inv_le_comm₀ hu (by positivity), inv_div]
      have := not_lt.mp h1
      linarith
    have h3 : 2 * |deriv p ‖v‖| * ‖v‖⁻¹ ≤ cutoffConstant ρ * |deriv p ‖v‖| := by
      have h4 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 2 * |deriv p ‖v‖|)
      refine h4.trans (le_of_eq ?_)
      unfold cutoffConstant
      field_simp
      ring
    linarith
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem cutoffSlope_eq_sum (p : ℝ → ℝ) (e η : BondField ι) :
    cutoffSlope p e η = ∑ b, bondCutoffSlope p (e b) (η b) := rfl
theorem contDiffOn_cutoffSlope (hpow : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (e : BondField ι) : ContDiffOn ℝ 1 (cutoffSlope p e) {η | ∀ b, ‖η b‖ < ρ} := by
  intro η hη
  have h : ContDiffAt ℝ 1 (cutoffSlope p e) η := by
    have e1 : cutoffSlope p e = fun η => ∑ b, bondCutoffSlope p (e b) (η b) := rfl
    rw [e1]
    refine ContDiffAt.sum fun b _ => ?_
    have hpr : ContDiffAt ℝ 1 (fun ζ : BondField ι => ζ b) η :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).contDiff.contDiffAt
    exact ContDiffAt.comp (g := bondCutoffSlope p (e b)) (f := fun ζ : BondField ι => ζ b) η
      (contDiffAt_bondCutoffSlope hpow hρ hp (e b) (hη b)) hpr
  exact h.contDiffWithinAt
theorem bondGradNorm_cutoffSlope_le (hpow : cutoffDerivBoundsStatement) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (e : BondField ι) (b : ι) {η : BondField ι} (hη : ∀ b, ‖η b‖ < ρ) :
    bondGradNorm (cutoffSlope p e) b η ≤
      (|iteratedDeriv 2 p ‖η b‖| + cutoffConstant ρ * |iteratedDeriv 1 p ‖η b‖|) * ‖e b‖ := by
  have hd : ∀ b' : ι, HasFDerivAt (fun ζ : BondField ι => bondCutoffSlope p (e b') (ζ b'))
      ((fderiv ℝ (bondCutoffSlope p (e b')) (η b')).comp (ContinuousLinearMap.proj b')) η := fun b' =>
    HasFDerivAt.comp (g := bondCutoffSlope p (e b')) (f := fun ζ : BondField ι => ζ b') η
      ((contDiffAt_bondCutoffSlope hpow hρ hp (e b') (hη b')).differentiableAt (by norm_num)).hasFDerivAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b').hasFDerivAt
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun b' _ => hd b')
  have hf : fderiv ℝ (cutoffSlope p e) η =
      ∑ b', (fderiv ℝ (bondCutoffSlope p (e b')) (η b')).comp (ContinuousLinearMap.proj b') := hs.fderiv
  unfold bondGradNorm
  rw [hf]
  have hc : (∑ b', (fderiv ℝ (bondCutoffSlope p (e b')) (η b')).comp (ContinuousLinearMap.proj b')).comp
      (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) = fderiv ℝ (bondCutoffSlope p (e b)) (η b) := by
    ext w
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.proj_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Pi.single_eq_of_ne hb']
    · intro h
      exact absurd (Finset.mem_univ b) h
  rw [hc]
  exact norm_fderiv_bondCutoffSlope_le hpow hρ hp (e b) (hη b)
theorem ballExpectation_mono {r : ℝ → ℝ} {Φ f g : BondField ι → ℝ}
    (hD : ∀ η, 0 ≤ ballDensity r Φ η) (hf : Integrable fun η => f η * ballDensity r Φ η)
    (hg : Integrable fun η => g η * ballDensity r Φ η)
    (hle : ∀ η, f η * ballDensity r Φ η ≤ g η * ballDensity r Φ η) :
    ballExpectation r Φ f ≤ ballExpectation r Φ g :=
  div_le_div_of_nonneg_right (integral_mono hf hg hle) (integral_nonneg hD)
theorem aestronglyMeasurable_mul_of_vanishing {U : Set (BondField ι)} (hU : IsOpen U)
    {f D : BondField ι → ℝ} (hf : ContinuousOn f U) (hD : AEStronglyMeasurable D volume)
    (h0 : ∀ η, η ∉ U → D η = 0) :
    AEStronglyMeasurable (fun η => f η * D η) volume := by apply _root_.YangMills.Construction.BondIntegration.FieldScoreSize.aestronglyMeasurable_mul_of_vanishing <;> assumption
def slopeSizeConstant (ρ : ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (n N q : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ 2 * (1 + cutoffConstant ρ) * (1 + |Cr 1 q (q * N)|) * (1 + |Cr 2 q (q * N)|)
theorem pow_card_mul_le_slopeBase {c a₁ a₂ : ℝ} {n : ℕ} {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ n) (hc : 0 ≤ c)
    (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (m : ℕ) :
    k ^ m * k * a₁ ≤ (((n : ℝ) + 2) ^ 2 * (1 + c) * (1 + a₁) * (1 + a₂)) ^ (m + 1) := by
  have hb : ((n : ℝ) + 2) * (1 + a₁) ≤ ((n : ℝ) + 2) ^ 2 * (1 + c) * (1 + a₁) * (1 + a₂) := by
    have e1 : (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
    have e2 : ((n : ℝ) + 2) ^ 2 ≤ ((n : ℝ) + 2) ^ 2 * (1 + c) * (1 + a₂) := by
      have : 1 ≤ (1 + c) * (1 + a₂) := by nlinarith
      nlinarith [sq_nonneg ((n : ℝ) + 2)]
    calc ((n : ℝ) + 2) * (1 + a₁) ≤ ((n : ℝ) + 2) ^ 2 * (1 + c) * (1 + a₂) * (1 + a₁) :=
          mul_le_mul_of_nonneg_right (e1.trans e2) (by linarith)
      _ = _ := by ring
  refine le_trans ?_ (pow_le_pow_left₀ (by positivity) hb _)
  rw [mul_pow]
  have h1 : k ^ (m + 1) ≤ ((n : ℝ) + 2) ^ (m + 1) := pow_le_pow_left₀ hk0 (by linarith) _
  have h2 : a₁ ≤ (1 + a₁) ^ (m + 1) := by
    have : (1 + a₁) ≤ (1 + a₁) ^ (m + 1) := le_self_pow₀ (by linarith) (by omega)
    linarith
  calc k ^ m * k * a₁ = k ^ (m + 1) * a₁ := by rw [pow_succ]
    _ ≤ _ := mul_le_mul h1 h2 h₁ (by positivity)
theorem two_pow_mul_le_slopeBase {c a₁ a₂ : ℝ} {n : ℕ} (hc : 0 ≤ c) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (m : ℕ) :
    2 ^ m * (a₂ + c ^ (m + 1) * a₁) ≤
      (((n : ℝ) + 2) ^ 2 * (1 + c) * (1 + a₁) * (1 + a₂)) ^ (m + 1) := by
  have hb : 2 * ((1 + c) * (1 + a₁) * (1 + a₂)) ≤
      ((n : ℝ) + 2) ^ 2 * (1 + c) * (1 + a₁) * (1 + a₂) := by
    have e1 : (2 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have e2 : 0 ≤ (1 + c) * (1 + a₁) * (1 + a₂) := by positivity
    calc 2 * ((1 + c) * (1 + a₁) * (1 + a₂)) ≤ ((n : ℝ) + 2) ^ 2 * ((1 + c) * (1 + a₁) * (1 + a₂)) :=
          mul_le_mul_of_nonneg_right e1 e2
      _ = _ := by ring
  refine le_trans ?_ (pow_le_pow_left₀ (by positivity) hb _)
  rw [mul_pow, mul_pow, mul_pow, pow_succ (2 : ℝ) m]
  obtain ⟨A, hA⟩ : ∃ A, A = (1 + c) ^ (m + 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (1 + a₁) ^ (m + 1) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (1 + a₂) ^ (m + 1) := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hD]
  have hA1 : 1 ≤ A := by
    rw [hA]
    exact one_le_pow₀ (by linarith)
  have hB1 : 1 + a₁ ≤ B := by
    rw [hB]
    exact le_self_pow₀ (by linarith) (by omega)
  have hD1 : 1 + a₂ ≤ D := by
    rw [hD]
    exact le_self_pow₀ (by linarith) (by omega)
  have hAc : c ^ (m + 1) ≤ A := by
    rw [hA]
    exact pow_le_pow_left₀ hc (by linarith) _
  have hAB : 1 ≤ A * B := by nlinarith
  have h3 : a₂ ≤ A * B * D := by nlinarith
  have h4 : c ^ (m + 1) * a₁ ≤ A * B * D := by
    have h5 : c ^ (m + 1) * a₁ ≤ A * B := mul_le_mul hAc (by linarith) h₁ (by linarith)
    have h6 : A * B ≤ A * B * D := by
      have : 1 ≤ D := by linarith
      nlinarith
    linarith
  have h7 : a₂ + c ^ (m + 1) * a₁ ≤ 2 * (A * B * D) := by linarith
  have h8 : (0 : ℝ) ≤ 2 ^ m := by positivity
  calc 2 ^ m * (a₂ + c ^ (m + 1) * a₁) ≤ 2 ^ m * (2 * (A * B * D)) :=
        mul_le_mul_of_nonneg_left h7 h8
    _ = _ := by ring
end CutoffSlope
open CutoffSlope in
theorem cutoffSlopeSize_holds (hpow : cutoffDerivBoundsStatement) :
    cutoffSlopeSize := by
  intro ρ p Cr n N hρ hp
  have hc0 : 0 ≤ cutoffConstant ρ := by
    unfold cutoffConstant
    positivity
  refine ⟨slopeSizeConstant ρ Cr n N, fun q => ?_, ?_⟩
  · unfold slopeSizeConstant
    positivity
  intro ι _ _ x κ C Cq₀ d Φ S dZ e E₀ hx hE hS hL hI he hdZ heb
  set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_apply b).norm continuous_const
  set D : BondField ι → ℝ := ballDensity (cutoffFactor ρ p) Φ with hDdef
  have hcut0 : ∀ u, 0 ≤ cutoffFactor ρ p u := fun u => by
    unfold cutoffFactor
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hD0 : ∀ η, 0 ≤ D η := fun η =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => hcut0 _) (Real.exp_pos _).le
  have hDoff : ∀ η, η ∉ U → D η = 0 := by
    intro η hη
    have h1 : ¬ ∀ b, ‖η b‖ < ρ := hη
    push Not at h1
    obtain ⟨b, hb⟩ := h1
    show radialWeightProd (cutoffFactor ρ p) η * _ = 0
    unfold radialWeightProd
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb]), zero_mul]
  have hDm : AEStronglyMeasurable D volume := hI.aestronglyMeasurable
  have hc := contDiffOn_cutoffSlope hpow hρ hp e
  refine ⟨hc, ⟨fun η hη => ?_, 0, fun q hq => ?_⟩⟩
  · exact ((hc.contDiffAt (hUo.mem_nhds hη)).differentiableAt (by norm_num))
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  set y : ℝ := (x ^ N)⁻¹ with hy
  have hx0 : 0 < x := by linarith
  have hyq : (x ^ ((m + 1) * N))⁻¹ = y ^ (m + 1) := by
    rw [hy, inv_pow, ← pow_mul, mul_comm]
  set a₁ : ℝ := |Cr 1 (m + 1) ((m + 1) * N)| with ha₁
  set a₂ : ℝ := |Cr 2 (m + 1) ((m + 1) * N)| with ha₂
  have hP1 := fun b => hL.cutoff_deriv_moments 1 (m + 1) ((m + 1) * N) b le_rfl (by omega)
  have hP2 := fun b => hL.cutoff_deriv_moments 2 (m + 1) ((m + 1) * N) b (by norm_num) (by omega)
  refine ⟨?_, fun b => ?_⟩
  · set K : ℝ := E₀ ^ (m + 1) * (S.card : ℝ) ^ m with hK
    have hK0 : 0 ≤ K := by positivity
    let g : BondField ι → ℝ := fun η =>
      K * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ (m + 1)
    have hgi : Integrable fun η => g η * D η := by
      have h1 : Integrable fun η => K * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ (m + 1) * D η :=
        (integrable_finset_sum _ fun b _ => (hP1 b).1).const_mul K
      refine h1.congr (Filter.Eventually.of_forall fun η => ?_)
      show K * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ (m + 1) * D η =
        (K * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ (m + 1)) * D η
      rw [mul_assoc K, Finset.sum_mul]
    have hpt : ∀ η ∈ U, |cutoffSlope p e η - 0| ^ (m + 1) ≤ g η := by
      intro η hη
      rw [sub_zero]
      have h1 : |cutoffSlope p e η| ≤ E₀ * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| := by
        rw [cutoffSlope_eq_sum, ← Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => by
          rw [he b hb]
          simp [bondCutoffSlope]), Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        refine (abs_bondCutoffSlope_le _ _).trans ?_
        rw [iteratedDeriv_one, mul_comm]
        exact mul_le_mul_of_nonneg_right (heb b) (abs_nonneg _)
      have h2 : (∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖|) ^ (m + 1) ≤
          (S.card : ℝ) ^ m * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ (m + 1) :=
        pow_sum_le_card_mul_sum_pow (fun b _ => abs_nonneg _) m
      calc |cutoffSlope p e η| ^ (m + 1)
          ≤ (E₀ * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖|) ^ (m + 1) :=
            pow_le_pow_left₀ (abs_nonneg _) h1 _
        _ = E₀ ^ (m + 1) * (∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖|) ^ (m + 1) := mul_pow _ _ _
        _ ≤ E₀ ^ (m + 1) * ((S.card : ℝ) ^ m * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = g η := by
            show _ = K * _
            rw [hK]
            ring
    have hle : ∀ η, |cutoffSlope p e η - 0| ^ (m + 1) * D η ≤ g η * D η := by
      intro η
      by_cases hη : η ∈ U
      · exact mul_le_mul_of_nonneg_right (hpt η hη) (hD0 η)
      · rw [hDoff η hη, mul_zero, mul_zero]
    have hfm : AEStronglyMeasurable (fun η => |cutoffSlope p e η - 0| ^ (m + 1) * D η) volume :=
      aestronglyMeasurable_mul_of_vanishing hUo ((hc.continuousOn.sub continuousOn_const).abs.pow _) hDm hDoff
    have hfi : Integrable fun η => |cutoffSlope p e η - 0| ^ (m + 1) * D η := by
      refine hgi.mono' hfm (Filter.Eventually.of_forall fun η => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hD0 η))]
      exact hle η
    refine ⟨hfi, (ballExpectation_mono hD0 hfi hgi hle).trans ?_⟩
    have hmean : ballExpectation (cutoffFactor ρ p) Φ g ≤ K * ((S.card : ℝ) * (a₁ * y ^ (m + 1))) := by
      have e1 : ballExpectation (cutoffFactor ρ p) Φ g =
          K * ∑ b ∈ S, ballExpectation (cutoffFactor ρ p) Φ fun η => |iteratedDeriv 1 p ‖η b‖| ^ (m + 1) := by
        unfold ballExpectation
        have e2 : ∫ η, g η * ballDensity (cutoffFactor ρ p) Φ η =
            K * ∑ b ∈ S, ∫ η, |iteratedDeriv 1 p ‖η b‖| ^ (m + 1) * ballDensity (cutoffFactor ρ p) Φ η := by
          rw [← integral_finsetSum _ fun b _ => (hP1 b).1, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
          show (K * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ (m + 1)) * _ = _
          rw [mul_assoc K, Finset.sum_mul]
        rw [e2, mul_div_assoc, Finset.sum_div]
      rw [e1]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      calc ∑ b ∈ S, ballExpectation (cutoffFactor ρ p) Φ (fun η => |iteratedDeriv 1 p ‖η b‖| ^ (m + 1))
          ≤ ∑ _b ∈ S, a₁ * y ^ (m + 1) := Finset.sum_le_sum fun b _ => by
            refine (hP1 b).2.trans ?_
            rw [hyq]
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = _ := by simp
    refine hmean.trans ?_
    have hnum := pow_card_mul_le_slopeBase (c := cutoffConstant ρ) (a₁ := a₁) (a₂ := a₂) (n := n)
      (k := (S.card : ℝ)) (Nat.cast_nonneg _) (by exact_mod_cast hS) hc0 (abs_nonneg _) (abs_nonneg _) m
    have hsz : (slopeSizeConstant ρ Cr n N (m + 1) * (E₀ * y)) ^ (m + 1) =
        (((n : ℝ) + 2) ^ 2 * (1 + cutoffConstant ρ) * (1 + a₁) * (1 + a₂)) ^ (m + 1) *
          (E₀ ^ (m + 1) * y ^ (m + 1)) := by
      rw [mul_pow, mul_pow]
      rfl
    rw [hsz, hK]
    have hpos : 0 ≤ E₀ ^ (m + 1) * y ^ (m + 1) := by positivity
    calc E₀ ^ (m + 1) * (S.card : ℝ) ^ m * ((S.card : ℝ) * (a₁ * y ^ (m + 1)))
        = (S.card : ℝ) ^ m * S.card * a₁ * (E₀ ^ (m + 1) * y ^ (m + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hnum hpos
  · obtain ⟨c, hcdef⟩ : ∃ c, c = cutoffConstant ρ := ⟨_, rfl⟩
    have hcont : ContinuousOn (bondGradNorm (cutoffSlope p e) b) U := by
      have hf : ContinuousOn (fderiv ℝ (cutoffSlope p e)) U :=
        hc.continuousOn_fderiv_of_isOpen hUo le_rfl
      exact (hf.clm_comp continuousOn_const).norm
    have hfm : AEStronglyMeasurable
        (fun η => |bondGradNorm (cutoffSlope p e) b η| ^ (m + 1) * D η) volume :=
      aestronglyMeasurable_mul_of_vanishing hUo (hcont.abs.pow _) hDm hDoff
    have hB0 : 0 ≤ slopeSizeConstant ρ Cr n N (m + 1) * Real.sqrt x * (E₀ * y) *
        Real.exp (-(2 * κ * dZ b)) := by
      have : 0 ≤ slopeSizeConstant ρ Cr n N (m + 1) := by
        unfold slopeSizeConstant
        positivity
      positivity
    by_cases hb : b ∈ S
    · let g : BondField ι → ℝ := fun η => E₀ ^ (m + 1) * 2 ^ m *
        (|iteratedDeriv 2 p ‖η b‖| ^ (m + 1) + c ^ (m + 1) * |iteratedDeriv 1 p ‖η b‖| ^ (m + 1))
      have hgi : Integrable fun η => g η * D η := by
        have h1 := ((hP2 b).1.add ((hP1 b).1.const_mul (c ^ (m + 1)))).const_mul (E₀ ^ (m + 1) * 2 ^ m)
        refine h1.congr (Filter.Eventually.of_forall fun η => ?_)
        simp only [Pi.add_apply, g]
        ring
      have hpt : ∀ η ∈ U, |bondGradNorm (cutoffSlope p e) b η| ^ (m + 1) ≤ g η := by
        intro η hη
        have h1 := bondGradNorm_cutoffSlope_le hpow hρ hp e b hη
        rw [← hcdef] at h1
        have h0 : 0 ≤ bondGradNorm (cutoffSlope p e) b η := norm_nonneg _
        rw [abs_of_nonneg h0]
        have hcc : 0 ≤ c := by
          rw [hcdef]
          exact hc0
        have h2 : bondGradNorm (cutoffSlope p e) b η ≤
            (|iteratedDeriv 2 p ‖η b‖| + c * |iteratedDeriv 1 p ‖η b‖|) * E₀ :=
          h1.trans (mul_le_mul_of_nonneg_left (heb b) (by positivity))
        have h3 := add_pow_le (abs_nonneg (iteratedDeriv 2 p ‖η b‖))
          (mul_nonneg hcc (abs_nonneg (iteratedDeriv 1 p ‖η b‖))) (m + 1)
        rw [Nat.add_sub_cancel, mul_pow c] at h3
        calc bondGradNorm (cutoffSlope p e) b η ^ (m + 1)
            ≤ ((|iteratedDeriv 2 p ‖η b‖| + c * |iteratedDeriv 1 p ‖η b‖|) * E₀) ^ (m + 1) :=
              pow_le_pow_left₀ h0 h2 _
          _ = (|iteratedDeriv 2 p ‖η b‖| + c * |iteratedDeriv 1 p ‖η b‖|) ^ (m + 1) * E₀ ^ (m + 1) :=
              mul_pow _ _ _
          _ ≤ (2 ^ m * (|iteratedDeriv 2 p ‖η b‖| ^ (m + 1) +
                c ^ (m + 1) * |iteratedDeriv 1 p ‖η b‖| ^ (m + 1))) * E₀ ^ (m + 1) :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = g η := by
              show _ = E₀ ^ (m + 1) * 2 ^ m * _
              ring
      have hle : ∀ η, |bondGradNorm (cutoffSlope p e) b η| ^ (m + 1) * D η ≤ g η * D η := by
        intro η
        by_cases hη : η ∈ U
        · exact mul_le_mul_of_nonneg_right (hpt η hη) (hD0 η)
        · rw [hDoff η hη, mul_zero, mul_zero]
      have hfi : Integrable fun η => |bondGradNorm (cutoffSlope p e) b η| ^ (m + 1) * D η := by
        refine hgi.mono' hfm (Filter.Eventually.of_forall fun η => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hD0 η))]
        exact hle η
      refine ⟨hfi, (ballExpectation_mono hD0 hfi hgi hle).trans ?_⟩
      have hmean : ballExpectation (cutoffFactor ρ p) Φ g ≤
          E₀ ^ (m + 1) * 2 ^ m * ((a₂ + c ^ (m + 1) * a₁) * y ^ (m + 1)) := by
        have e2 : ∫ η, g η * ballDensity (cutoffFactor ρ p) Φ η = E₀ ^ (m + 1) * 2 ^ m *
            ((∫ η, |iteratedDeriv 2 p ‖η b‖| ^ (m + 1) * ballDensity (cutoffFactor ρ p) Φ η) +
              c ^ (m + 1) * ∫ η, |iteratedDeriv 1 p ‖η b‖| ^ (m + 1) *
                ballDensity (cutoffFactor ρ p) Φ η) := by
          rw [← integral_const_mul (c ^ (m + 1)), ← integral_add (hP2 b).1
            ((hP1 b).1.const_mul _), ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
          simp only [g]
          ring
        unfold ballExpectation at *
        rw [e2, mul_div_assoc, add_div, mul_div_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have b1 := (hP2 b).2
        have b2 := (hP1 b).2
        rw [hyq] at b1 b2
        have b3 : (Cr 2 (m + 1) ((m + 1) * N)) * y ^ (m + 1) ≤ a₂ * y ^ (m + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        have b4 : (Cr 1 (m + 1) ((m + 1) * N)) * y ^ (m + 1) ≤ a₁ * y ^ (m + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        have b5 : 0 ≤ c ^ (m + 1) := by rw [hcdef]; positivity
        have b6 := mul_le_mul_of_nonneg_left (b2.trans b4) b5
        have e3 : (a₂ + c ^ (m + 1) * a₁) * y ^ (m + 1) =
            a₂ * y ^ (m + 1) + c ^ (m + 1) * (a₁ * y ^ (m + 1)) := by ring
        rw [e3]
        exact add_le_add (b1.trans b3) b6
      refine hmean.trans ?_
      have hnum := two_pow_mul_le_slopeBase (c := cutoffConstant ρ) (a₁ := a₁) (a₂ := a₂) (n := n) hc0
        (abs_nonneg _) (abs_nonneg _) m
      rw [← hcdef] at hnum
      rw [hdZ b hb]
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      have hs1 : 1 ≤ Real.sqrt x := by
        rw [Real.one_le_sqrt]
        exact hx
      have hsz0 : 0 ≤ slopeSizeConstant ρ Cr n N (m + 1) := by
        unfold slopeSizeConstant
        positivity
      have h5 : slopeSizeConstant ρ Cr n N (m + 1) * (E₀ * y) ≤
          slopeSizeConstant ρ Cr n N (m + 1) * Real.sqrt x * (E₀ * y) := by
        have h6 : slopeSizeConstant ρ Cr n N (m + 1) ≤ slopeSizeConstant ρ Cr n N (m + 1) * Real.sqrt x :=
          le_mul_of_one_le_right hsz0 hs1
        exact mul_le_mul_of_nonneg_right h6 (by positivity)
      refine le_trans ?_ (pow_le_pow_left₀ (by positivity) h5 _)
      have hsz : (slopeSizeConstant ρ Cr n N (m + 1) * (E₀ * y)) ^ (m + 1) =
          (((n : ℝ) + 2) ^ 2 * (1 + c) * (1 + a₁) * (1 + a₂)) ^ (m + 1) *
            (E₀ ^ (m + 1) * y ^ (m + 1)) := by
        rw [mul_pow, mul_pow, hcdef]
        rfl
      rw [hsz]
      have hpos : 0 ≤ E₀ ^ (m + 1) * y ^ (m + 1) := by positivity
      calc E₀ ^ (m + 1) * 2 ^ m * ((a₂ + c ^ (m + 1) * a₁) * y ^ (m + 1))
          = 2 ^ m * (a₂ + c ^ (m + 1) * a₁) * (E₀ ^ (m + 1) * y ^ (m + 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hnum hpos
    · have hz : ∀ η ∈ U, bondGradNorm (cutoffSlope p e) b η = 0 := by
        intro η hη
        have h1 := bondGradNorm_cutoffSlope_le hpow hρ hp e b hη
        rw [he b hb, norm_zero, mul_zero] at h1
        exact le_antisymm h1 (norm_nonneg _)
      have hzero : (fun η => |bondGradNorm (cutoffSlope p e) b η| ^ (m + 1) * D η) = fun _ => 0 := by
        funext η
        by_cases hη : η ∈ U
        · rw [hz η hη]
          simp
        · rw [hDoff η hη, mul_zero]
      refine ⟨by rw [hzero]; exact integrable_zero _ _ _, ?_⟩
      unfold ballExpectation
      have hzero' : (fun η => |bondGradNorm (cutoffSlope p e) b η| ^ (m + 1) *
          ballDensity (cutoffFactor ρ p) Φ η) = fun _ => 0 := hzero
      rw [hzero']
      simp only [integral_zero, zero_div]
      positivity
end YangMills.Construction.Estimates
end
