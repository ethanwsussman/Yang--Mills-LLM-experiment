import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACutProof
import YangMills.Construction.SummableBoundsOfTheFlow.RadialSlopeOfACut
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace ContDiff
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Estimates
private theorem hasFDerivAt_norm_of_ne_zero {v : BondVector} (hv : v ≠ 0) :
    HasFDerivAt (fun u : BondVector => ‖u‖) (‖v‖⁻¹ • innerSL ℝ v) v := by
  have hn : DifferentiableAt ℝ (fun u : BondVector => ‖u‖) v :=
    (contDiffAt_norm ℝ hv (n := 1)).differentiableAt one_ne_zero
  have h1 := hn.hasFDerivAt
  have h2 : HasFDerivAt (fun u : BondVector => ‖u‖ ^ 2)
      ((2 * ‖v‖) • fderiv ℝ (fun u : BondVector => ‖u‖) v) v := by
    have := h1.mul h1
    have e : (fun u : BondVector => ‖u‖ * ‖u‖) = fun u => ‖u‖ ^ 2 := by
      funext u
      ring
    have e2 : ‖v‖ • fderiv ℝ (fun u : BondVector => ‖u‖) v + ‖v‖ • fderiv ℝ (fun u : BondVector => ‖u‖) v =
        (2 * ‖v‖) • fderiv ℝ (fun u : BondVector => ‖u‖) v := by
      rw [← add_smul]
      congr 1
      ring
    simp only [Pi.mul_def] at this
    rw [e, e2] at this
    exact this
  have h3 := (hasStrictFDerivAt_norm_sq v).hasFDerivAt
  have e := h2.unique h3
  have hr : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have e3 : fderiv ℝ (fun u : BondVector => ‖u‖) v = ‖v‖⁻¹ • innerSL ℝ v := by
    have : (2 * ‖v‖)⁻¹ • ((2 * ‖v‖) • fderiv ℝ (fun u : BondVector => ‖u‖) v) =
        (2 * ‖v‖)⁻¹ • (2 • innerSL ℝ v) := by rw [e]
    rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at this
    rw [this]
    ext h
    simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
    field_simp
    norm_num
  rw [← e3]
  exact h1
abbrev _root_.YangMills.SharedProofs.p11430 := @hasFDerivAt_norm_of_ne_zero
private theorem hasFDerivAt_comp_norm {f : ℝ → ℝ} {g : ℝ} {v : BondVector} (hv : v ≠ 0)
    (hf : HasDerivAt f (‖v‖ * g) ‖v‖) :
    HasFDerivAt (fun u : BondVector => f ‖u‖) (g • innerSL ℝ v) v := by
  have := hf.comp_hasFDerivAt v (hasFDerivAt_norm_of_ne_zero hv)
  have hr : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have e : (‖v‖ * g) • (‖v‖⁻¹ • innerSL ℝ v) = g • innerSL ℝ v := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [e] at this
  exact this
variable {ρ : ℝ} {p : ℝ → ℝ}
private theorem contDiffOn_deriv_of_isCutoff (h : IsCutoff ρ p) :
    ContDiffOn ℝ ∞ (deriv p) (Set.Ioo 0 ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.cutoff_deriv_contDiffOn <;> assumption
private theorem contDiffOn_deriv2_of_isCutoff (h : IsCutoff ρ p) :
    ContDiffOn ℝ ∞ (deriv (deriv p)) (Set.Ioo 0 ρ) :=
  (contDiffOn_deriv_of_isCutoff h).deriv_of_isOpen isOpen_Ioo (by simp)
private theorem hasDerivAt_of_contDiffOn_Ioo {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Set.Ioo 0 ρ)) {r : ℝ}
    (hr : r ∈ Set.Ioo 0 ρ) : HasDerivAt f (deriv f r) r :=
  (((hf r hr).contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
private def radialQuot₀ (p : ℝ → ℝ) (r : ℝ) : ℝ := deriv p r * r⁻¹
private def radialQuot₁ (p : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv p) r * (r⁻¹) ^ 2 - deriv p r * (r⁻¹) ^ 3
private def radialQuot₂ (p : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv (deriv p)) r * (r⁻¹) ^ 3 - 3 * (deriv (deriv p) r * (r⁻¹) ^ 4) + 3 * (deriv p r * (r⁻¹) ^ 5)
private theorem hasDerivAt_inv_pow' {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    HasDerivAt (fun u : ℝ => (u⁻¹) ^ n) (-(n : ℝ) * (r⁻¹) ^ (n + 1)) r := by
  have h : HasDerivAt (fun u : ℝ => (u⁻¹) ^ n) _ r := (hasDerivAt_inv hr).fun_pow n
  refine h.congr_deriv ?_
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
private theorem hasDerivAt_radialQuot₀ (h : IsCutoff ρ p) {r : ℝ} (hr : r ∈ Set.Ioo 0 ρ) :
    HasDerivAt (radialQuot₀ p) (r * radialQuot₁ p r) r := by
  have h0 : r ≠ 0 := hr.1.ne'
  have h2 : HasDerivAt (fun u : ℝ => deriv p u * u⁻¹) _ r :=
    (hasDerivAt_of_contDiffOn_Ioo (contDiffOn_deriv_of_isCutoff h) hr).fun_mul (hasDerivAt_inv h0)
  refine HasDerivAt.congr_deriv (f := radialQuot₀ p) h2 ?_
  unfold radialQuot₁
  field_simp
  ring
private theorem hasDerivAt_radialQuot₁ (h : IsCutoff ρ p) {r : ℝ} (hr : r ∈ Set.Ioo 0 ρ) :
    HasDerivAt (radialQuot₁ p) (r * radialQuot₂ p r) r := by
  have h0 : r ≠ 0 := hr.1.ne'
  have h2 : HasDerivAt (fun u : ℝ => deriv (deriv p) u * (u⁻¹) ^ 2 - deriv p u * (u⁻¹) ^ 3) _ r :=
    ((hasDerivAt_of_contDiffOn_Ioo (contDiffOn_deriv2_of_isCutoff h) hr).fun_mul
      (hasDerivAt_inv_pow' h0 2)).fun_sub
      ((hasDerivAt_of_contDiffOn_Ioo (contDiffOn_deriv_of_isCutoff h) hr).fun_mul (hasDerivAt_inv_pow' h0 3))
  refine HasDerivAt.congr_deriv (f := radialQuot₁ p) h2 ?_
  unfold radialQuot₂
  push_cast
  field_simp
  ring
private theorem deriv_eq_zero_of_lt_of_isCutoff (h : IsCutoff ρ p) {r : ℝ} (h0 : 0 < r)
    (h1 : r < 5 * ρ / 8) : deriv p r = 0 := by
  have : p =ᶠ[nhds r] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds h0 h1] with u hu
    exact h.vanish_small u hu.1.le hu.2.le
  rw [this.deriv_eq]
  simp
private theorem radialDirectionalDeriv_eq_zero_of_lt (h : IsCutoff ρ p) (e : BondVector) {u : BondVector}
    (hu : ‖u‖ < 5 * ρ / 8) : radialDirectionalDeriv p e u = 0 := by
  by_cases h0 : u = 0
  · subst h0
    simp [radialDirectionalDeriv]
  · simp [radialDirectionalDeriv, deriv_eq_zero_of_lt_of_isCutoff h (norm_pos_iff.2 h0) hu]
private def innerBilin : BondVector →L[ℝ] BondVector →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => innerSL ℝ u
      map_add' := fun a b => by ext c; simp
      map_smul' := fun a b => by ext c; simp }
private theorem innerBilin_apply (a b : BondVector) : innerBilin a b = ⟪a, b⟫ := by
  simp [innerBilin]
private theorem norm_innerBilin_apply (a : BondVector) : ‖innerBilin a‖ = ‖a‖ := by
  have : innerBilin a = innerSL ℝ a := by
    ext c
    simp [innerBilin_apply]
  rw [this, innerSL_apply_norm]
private theorem norm_innerBilin_le : ‖innerBilin‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
  rw [norm_innerBilin_apply, one_mul]
private theorem hasFDerivAt_comp_norm' {f : ℝ → ℝ} {g : ℝ} {v : BondVector} (hv : v ≠ 0)
    (hf : HasDerivAt f (‖v‖ * g) ‖v‖) :
    HasFDerivAt (fun u : BondVector => f ‖u‖) (g • innerBilin v) v := by
  have : innerBilin v = innerSL ℝ v := by
    ext c
    simp [innerBilin_apply]
  rw [this]
  exact hasFDerivAt_comp_norm hv hf
private def radialDerivFDeriv (p : ℝ → ℝ) (e u : BondVector) : BondVector →L[ℝ] ℝ :=
  (radialQuot₁ p ‖u‖ * innerBilin e u) • innerBilin u + radialQuot₀ p ‖u‖ • innerBilin e
private theorem hasFDerivAt_radialDirectionalDeriv (h : IsCutoff ρ p) (e : BondVector) {u : BondVector}
    (h0 : u ≠ 0) (h1 : ‖u‖ < ρ) :
    HasFDerivAt (radialDirectionalDeriv p e) (radialDerivFDeriv p e u) u := by
  have hr : ‖u‖ ∈ Set.Ioo 0 ρ := ⟨norm_pos_iff.2 h0, h1⟩
  have h2 : HasFDerivAt (fun w : BondVector => radialQuot₀ p ‖w‖ * innerBilin e w) _ u :=
    (hasFDerivAt_comp_norm' h0 (hasDerivAt_radialQuot₀ h hr)).fun_mul (innerBilin e).hasFDerivAt
  have e1 : radialDirectionalDeriv p e = fun w : BondVector => radialQuot₀ p ‖w‖ * innerBilin e w := by
    funext w
    simp only [radialDirectionalDeriv, radialQuot₀, innerBilin_apply, real_inner_comm]
  rw [e1]
  refine h2.congr_fderiv ?_
  ext c
  simp only [radialDerivFDeriv, add_apply, smul_apply, smul_eq_mul]
  ring
private theorem hasFDerivAt_radialDerivFDeriv (h : IsCutoff ρ p) (e : BondVector) {v : BondVector}
    (h0 : v ≠ 0) (h1 : ‖v‖ < ρ) :
    HasFDerivAt (radialDerivFDeriv p e)
      (((radialQuot₁ p ‖v‖ * innerBilin e v) • innerBilin +
        (radialQuot₁ p ‖v‖ • innerBilin e +
          innerBilin e v • (radialQuot₂ p ‖v‖ • innerBilin v)).smulRight (innerBilin v)) +
        (radialQuot₁ p ‖v‖ • innerBilin v).smulRight (innerBilin e)) v := by
  have hr : ‖v‖ ∈ Set.Ioo 0 ρ := ⟨norm_pos_iff.2 h0, h1⟩
  have hA : HasFDerivAt (fun w : BondVector => radialQuot₁ p ‖w‖ * innerBilin e w) _ v :=
    (hasFDerivAt_comp_norm' h0 (hasDerivAt_radialQuot₁ h hr)).fun_mul (innerBilin e).hasFDerivAt
  have hC := hasFDerivAt_comp_norm' h0 (hasDerivAt_radialQuot₀ h hr)
  have hB : HasFDerivAt (fun w : BondVector => innerBilin w) innerBilin v := innerBilin.hasFDerivAt
  have := (hA.fun_smul hB).fun_add (hC.smul_const (innerBilin e))
  refine HasFDerivAt.congr_fderiv (f := radialDerivFDeriv p e) this ?_
  ext c d
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, innerBilin_apply]
private theorem norm_smul_add_smulRight_le {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (a : ℝ) (B : E →L[ℝ] G) (c₁ c₂ : E →L[ℝ] ℝ) (g₁ g₂ : G) :
    ‖(a • B + c₁.smulRight g₁) + c₂.smulRight g₂‖ ≤ |a| * ‖B‖ + ‖c₁‖ * ‖g₁‖ + ‖c₂‖ * ‖g₂‖ := by
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_smul, Real.norm_eq_abs]
  · rw [ContinuousLinearMap.norm_smulRight_apply]
  · rw [ContinuousLinearMap.norm_smulRight_apply]
set_option maxHeartbeats 1000000 in
theorem radialDirectionalDeriv_bound : radialDirectionalDerivBoundStatement := by
  intro ρ p hρ h
  obtain ⟨D, hD⟩ : ∃ D, D = 1 + 8 / (5 * ρ) := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = 1 + ρ := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by
    have : 0 < 8 / (5 * ρ) := by positivity
    linarith
  have hR1 : 1 ≤ R₁ := by linarith
  obtain ⟨S, hS⟩ : ∃ S, S = D ^ 5 * R₁ ^ 3 := ⟨_, rfl⟩
  have hS1 : 1 ≤ S := by
    rw [hS]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD1) (one_le_pow₀ hR1)
  refine ⟨16 * S, by linarith, fun e v hv => ?_⟩
  have hE : 0 ≤ ‖e‖ := norm_nonneg _
  have hR : 0 ≤ cutoffDerivSum p ‖v‖ := by
    unfold cutoffDerivSum
    positivity
  by_cases hv' : ‖v‖ < 5 * ρ / 8
  · have hball : Metric.ball (0 : BondVector) (5 * ρ / 8) ∈ nhds v :=
      Metric.isOpen_ball.mem_nhds (by simpa using hv')
    have ev0 : ∀ u : BondVector, ‖u‖ < 5 * ρ / 8 → radialDirectionalDeriv p e =ᶠ[nhds u] fun _ => 0 := by
      intro u hu
      filter_upwards [Metric.isOpen_ball.mem_nhds (show u ∈ Metric.ball (0 : BondVector) (5 * ρ / 8) by
        simpa using hu)] with w hw
      exact radialDirectionalDeriv_eq_zero_of_lt h e (by simpa using hw)
    have ev : radialDirectionalDeriv p e =ᶠ[nhds v] fun _ => 0 := ev0 v hv'
    have ev1 : fderiv ℝ (radialDirectionalDeriv p e) =ᶠ[nhds v] fun _ => 0 := by
      filter_upwards [hball] with u hu
      rw [(ev0 u (by simpa using hu)).fderiv_eq]
      simp
    have hK : 0 ≤ 16 * S * ‖e‖ * cutoffDerivSum p ‖v‖ := by positivity
    refine ⟨contDiffAt_const.congr_of_eventuallyEq ev, ?_, ?_, ?_⟩
    · rw [ev.eq_of_nhds]
      simpa using hK
    · rw [ev.fderiv_eq, fderiv_const_apply, norm_zero]
      exact hK
    · rw [ev1.fderiv_eq, fderiv_const_apply]
      exact le_trans (le_of_eq ContinuousLinearMap.opNorm_zero) hK
  have hr5 : 5 * ρ / 8 ≤ ‖v‖ := not_lt.1 hv'
  have hrpos : 0 < ‖v‖ := by
    have : 0 < 5 * ρ / 8 := by positivity
    linarith
  have h0 : v ≠ 0 := norm_pos_iff.1 hrpos
  have hr : ‖v‖ ∈ Set.Ioo 0 ρ := ⟨hrpos, hv⟩
  have hU : {u : BondVector | u ≠ 0 ∧ ‖u‖ < ρ} ∈ nhds v := by
    have : IsOpen {u : BondVector | u ≠ 0 ∧ ‖u‖ < ρ} :=
      (isOpen_ne).inter (isOpen_lt continuous_norm continuous_const)
    exact this.mem_nhds ⟨h0, hv⟩
  have ev : fderiv ℝ (radialDirectionalDeriv p e) =ᶠ[nhds v] radialDerivFDeriv p e := by
    filter_upwards [hU] with u hu
    exact (hasFDerivAt_radialDirectionalDeriv h e hu.1 hu.2).fderiv
  have hsm : ContDiffAt ℝ 2 (radialDirectionalDeriv p e) v := by
    have hn : ContDiffAt ℝ 2 (fun u : BondVector => ‖u‖) v := contDiffAt_norm ℝ h0
    have h1 : ContDiffAt ℝ 2 (deriv p) ‖v‖ :=
      (((contDiffOn_deriv_of_isCutoff h) _ hr).contDiffAt (isOpen_Ioo.mem_nhds hr)).of_le ENat.LEInfty.out
    have h2 := ((h1.comp v hn).mul (hn.inv (norm_ne_zero_iff.2 h0))).mul
      (contDiffAt_id.inner ℝ (contDiffAt_const (c := e)))
    exact h2
  obtain ⟨i, hi⟩ : ∃ i, i = ‖v‖⁻¹ := ⟨_, rfl⟩
  have hi0 : 0 ≤ i := by rw [hi]; positivity
  have hiD : i ≤ D := by
    have h1 : ‖v‖⁻¹ ≤ (5 * ρ / 8)⁻¹ := inv_anti₀ (by positivity) hr5
    have h2 : (5 * ρ / 8)⁻¹ = 8 / (5 * ρ) := by field_simp
    rw [hi, hD]
    linarith
  have pw : ∀ n : ℕ, n ≤ 5 → i ^ n ≤ D ^ 5 := fun n hn =>
    (pow_le_pow_left₀ hi0 hiD n).trans (pow_le_pow_right₀ hD1 hn)
  obtain ⟨P₁, hP₁⟩ : ∃ P, P = deriv p ‖v‖ := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P, P = deriv (deriv p) ‖v‖ := ⟨_, rfl⟩
  obtain ⟨P₃, hP₃⟩ : ∃ P, P = deriv (deriv (deriv p)) ‖v‖ := ⟨_, rfl⟩
  have hRs : cutoffDerivSum p ‖v‖ = |P₁| + |P₂| + |P₃| := by
    simp only [cutoffDerivSum, iteratedDeriv_succ, iteratedDeriv_zero, hP₁, hP₂, hP₃]
  have hp1 : |P₁| ≤ cutoffDerivSum p ‖v‖ := by
    rw [hRs]
    linarith [abs_nonneg P₂, abs_nonneg P₃]
  have hp2 : |P₂| ≤ cutoffDerivSum p ‖v‖ := by
    rw [hRs]
    linarith [abs_nonneg P₁, abs_nonneg P₃]
  have hp3 : |P₃| ≤ cutoffDerivSum p ‖v‖ := by
    rw [hRs]
    linarith [abs_nonneg P₁, abs_nonneg P₂]
  obtain ⟨W, hW⟩ : ∃ W, W = D ^ 5 * cutoffDerivSum p ‖v‖ := ⟨_, rfl⟩
  have term : ∀ (P : ℝ) (n : ℕ), n ≤ 5 → |P| ≤ cutoffDerivSum p ‖v‖ → |P * i ^ n| ≤ W := by
    intro P n hn hP
    rw [abs_mul, abs_of_nonneg (pow_nonneg hi0 n), hW, mul_comm]
    exact mul_le_mul (pw n hn) hP (abs_nonneg _) (by positivity)
  have ha₀ : |radialQuot₀ p ‖v‖| ≤ W := by
    have := term P₁ 1 (by norm_num) hp1
    simpa [radialQuot₀, hP₁, hi] using this
  have ha : |radialQuot₁ p ‖v‖| ≤ 2 * W := by
    have t1 := term P₂ 2 (by norm_num) hp2
    have t2 := term P₁ 3 (by norm_num) hp1
    have e1 : radialQuot₁ p ‖v‖ = P₂ * i ^ 2 - P₁ * i ^ 3 := by rw [hP₁, hP₂, hi]; rfl
    rw [e1]
    calc _ ≤ |P₂ * i ^ 2| + |P₁ * i ^ 3| := abs_sub _ _
      _ ≤ 2 * W := by linarith
  have hc : |radialQuot₂ p ‖v‖| ≤ 7 * W := by
    have t1 := term P₃ 3 (by norm_num) hp3
    have t2 := term P₂ 4 (by norm_num) hp2
    have t3 := term P₁ 5 (by norm_num) hp1
    have e1 : radialQuot₂ p ‖v‖ = P₃ * i ^ 3 - 3 * (P₂ * i ^ 4) + 3 * (P₁ * i ^ 5) := by
      rw [hP₁, hP₂, hP₃, hi]; rfl
    rw [e1]
    have a1 : |3 * (P₂ * i ^ 4)| = 3 * |P₂ * i ^ 4| := by rw [abs_mul]; norm_num
    have a2 : |3 * (P₁ * i ^ 5)| = 3 * |P₁ * i ^ 5| := by rw [abs_mul]; norm_num
    calc _ ≤ |P₃ * i ^ 3 - 3 * (P₂ * i ^ 4)| + |3 * (P₁ * i ^ 5)| := abs_add_le _ _
      _ ≤ |P₃ * i ^ 3| + |3 * (P₂ * i ^ 4)| + |3 * (P₁ * i ^ 5)| := by
        gcongr
        exact abs_sub _ _
      _ ≤ 7 * W := by rw [a1, a2]; linarith
  obtain ⟨r, hrd⟩ : ∃ r, r = ‖v‖ := ⟨_, rfl⟩
  obtain ⟨E, hEd⟩ : ∃ E, E = ‖e‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hrd]; positivity
  have hE0 : 0 ≤ E := by rw [hEd]; positivity
  have hrR : r ≤ R₁ := by rw [hrd, hR₁]; linarith [hv]
  obtain ⟨T, hT⟩ : ∃ T, T = S * cutoffDerivSum p ‖v‖ := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hWT : ∀ n : ℕ, n ≤ 3 → W * r ^ n ≤ T := by
    intro n hn
    have h1 : r ^ n ≤ R₁ ^ 3 := (pow_le_pow_left₀ hr0 hrR n).trans (pow_le_pow_right₀ hR1 hn)
    calc W * r ^ n ≤ W * R₁ ^ 3 := mul_le_mul_of_nonneg_left h1 hW0
      _ = T := by rw [hW, hT, hS]; ring
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hBe : ∀ a b : BondVector, |innerBilin a b| ≤ ‖a‖ * ‖b‖ := fun a b => by
    rw [innerBilin_apply]
    exact abs_real_inner_le_norm a b
  have hev : |innerBilin e v| ≤ E * r := by rw [hEd, hrd]; exact hBe e v
  obtain ⟨a₀, ha₀d⟩ : ∃ a, a = |radialQuot₀ p ‖v‖| := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a', a' = |radialQuot₁ p ‖v‖| := ⟨_, rfl⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = |radialQuot₂ p ‖v‖| := ⟨_, rfl⟩
  have ha₀0 : 0 ≤ a₀ := by rw [ha₀d]; positivity
  have ha0 : 0 ≤ a := by rw [had]; positivity
  have hc0 : 0 ≤ c := by rw [hcd]; positivity
  rw [← ha₀d] at ha₀
  rw [← had] at ha
  rw [← hcd] at hc
  have ar : ∀ n : ℕ, n ≤ 3 → a * r ^ n ≤ 2 * T := fun n hn => by
    have := mul_le_mul_of_nonneg_right ha (pow_nonneg hr0 n)
    have h2 := hWT n hn
    nlinarith
  have cr : ∀ n : ℕ, n ≤ 3 → c * r ^ n ≤ 7 * T := fun n hn => by
    have := mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 n)
    have h2 := hWT n hn
    nlinarith
  have a₀T : a₀ ≤ T := by
    have := hWT 0 (by norm_num)
    simp only [pow_zero, mul_one] at this
    linarith
  have goalT : ∀ B : ℝ, B ≤ 16 * (E * T) → B ≤ 16 * S * ‖e‖ * cutoffDerivSum p ‖v‖ := by
    intro B hB
    refine hB.trans (le_of_eq ?_)
    rw [hT, hEd]
    ring
  have hS0 : 0 ≤ S := by linarith
  have hET : 0 ≤ E * T := mul_nonneg hE0 hT0
  refine ⟨hsm, ?_, ?_, ?_⟩
  · refine goalT _ ?_
    have e1 : radialDirectionalDeriv p e v = P₁ * i * ⟪v, e⟫ := by rw [hP₁, hi]; rfl
    have h1 : |⟪v, e⟫| ≤ r * E := by rw [hrd, hEd]; exact abs_real_inner_le_norm v e
    have h2 : i * r = 1 := by
      rw [hi, hrd]
      exact inv_mul_cancel₀ hrpos.ne'
    have h3 : |P₁| ≤ T := by
      have : cutoffDerivSum p ‖v‖ ≤ T := by
        rw [hT]
        exact le_mul_of_one_le_left hR hS1
      linarith
    rw [e1, abs_mul, abs_mul, abs_of_nonneg hi0]
    calc |P₁| * i * |⟪v, e⟫| ≤ |P₁| * i * (r * E) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = |P₁| * E * (i * r) := by ring
      _ = E * |P₁| := by rw [h2]; ring
      _ ≤ E * T := mul_le_mul_of_nonneg_left h3 hE0
      _ ≤ 16 * (E * T) := by linarith
  · refine goalT _ ?_
    rw [(hasFDerivAt_radialDirectionalDeriv h e h0 hv).fderiv]
    unfold radialDerivFDeriv
    have n1 : ‖(radialQuot₁ p ‖v‖ * innerBilin e v) • innerBilin v‖ ≤ (a * (E * r)) * r := by
      rw [norm_smul, norm_innerBilin_apply, Real.norm_eq_abs, abs_mul, ← had, ← hrd]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hev ha0) hr0
    have n2 : ‖radialQuot₀ p ‖v‖ • innerBilin e‖ ≤ a₀ * E := by
      rw [norm_smul, norm_innerBilin_apply, Real.norm_eq_abs, ← ha₀d, ← hEd]
    have n3 : a * r ^ 2 ≤ 2 * T := ar 2 (by norm_num)
    calc _ ≤ ‖(radialQuot₁ p ‖v‖ * innerBilin e v) • innerBilin v‖ + ‖radialQuot₀ p ‖v‖ • innerBilin e‖ :=
          norm_add_le _ _
      _ ≤ (a * (E * r)) * r + a₀ * E := add_le_add n1 n2
      _ = E * (a * r ^ 2) + E * a₀ := by ring
      _ ≤ E * (2 * T) + E * T := add_le_add (mul_le_mul_of_nonneg_left n3 hE0)
          (mul_le_mul_of_nonneg_left a₀T hE0)
      _ ≤ 16 * (E * T) := by nlinarith
  · refine goalT _ ?_
    rw [(hasFDerivAt_radialDerivFDeriv h e h0 hv |>.congr_of_eventuallyEq ev).fderiv]
    refine (norm_smul_add_smulRight_le _ _ _ _ _ _).trans ?_
    have hvr : ‖innerBilin v‖ = r := by rw [norm_innerBilin_apply, hrd]
    have hve : ‖innerBilin e‖ = E := by rw [norm_innerBilin_apply, hEd]
    have n1 : |radialQuot₁ p ‖v‖ * innerBilin e v| * ‖innerBilin‖ ≤ a * (E * r) := by
      rw [abs_mul, ← had]
      calc a * |innerBilin e v| * ‖innerBilin‖ ≤ a * |innerBilin e v| * 1 :=
            mul_le_mul_of_nonneg_left norm_innerBilin_le (by positivity)
        _ = a * |innerBilin e v| := mul_one _
        _ ≤ a * (E * r) := mul_le_mul_of_nonneg_left hev ha0
    have n2 : ‖radialQuot₁ p ‖v‖ • innerBilin e + innerBilin e v • (radialQuot₂ p ‖v‖ • innerBilin v)‖ ≤
        a * E + (E * r) * (c * r) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, hve, Real.norm_eq_abs, ← had]
      · rw [norm_smul, norm_smul, hvr, Real.norm_eq_abs, Real.norm_eq_abs, ← hcd]
        exact mul_le_mul_of_nonneg_right hev (by positivity)
    have n3 : ‖radialQuot₁ p ‖v‖ • innerBilin e + innerBilin e v • (radialQuot₂ p ‖v‖ • innerBilin v)‖ *
        ‖innerBilin v‖ ≤ (a * E + (E * r) * (c * r)) * r := by
      rw [hvr]
      exact mul_le_mul_of_nonneg_right n2 hr0
    have n4 : ‖radialQuot₁ p ‖v‖ • innerBilin v‖ * ‖innerBilin e‖ ≤ (a * r) * E := by
      rw [hve, norm_smul, hvr, Real.norm_eq_abs, ← had]
    have m1 := ar 1 (by norm_num)
    have m3 := cr 3 (by norm_num)
    rw [pow_one] at m1
    calc _ ≤ a * (E * r) + (a * E + (E * r) * (c * r)) * r + (a * r) * E :=
          add_le_add (add_le_add n1 n3) n4
      _ = E * (3 * (a * r) + c * r ^ 3) := by ring
      _ ≤ E * (3 * (2 * T) + 7 * T) := by gcongr
      _ ≤ 16 * (E * T) := by nlinarith
end YangMills.Construction.Estimates
end
