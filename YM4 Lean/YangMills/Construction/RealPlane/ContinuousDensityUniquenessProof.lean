import YangMills.Construction.RealPlane.ContinuousDensityUniqueness
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.RealPlane.DensityUniqueness
variable {n : ℕ} {U : Set (Fin n → RealPlane)} {φ : Fin n → RealPlane → ℝ}
theorem isCompact_pi_tsupport (hφ : IsSmoothTestFamilyIn U φ) :
    IsCompact (Set.univ.pi fun i => tsupport (φ i)) :=
  isCompact_univ_pi fun i => hφ.2.1 i
theorem prod_eq_zero_of_notMem_pi_tsupport {x : Fin n → RealPlane}
    (hx : x ∉ Set.univ.pi fun i => tsupport (φ i)) : ∏ i, φ i (x i) = 0 := by
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
theorem continuous_prod_apply (hφ : IsSmoothTestFamilyIn U φ) :
    Continuous fun x : Fin n → RealPlane => ∏ i, φ i (x i) :=
  continuous_finsetProd _ fun i _ => (hφ.1 i).continuous.comp (continuous_apply i)
theorem productWeightedIntegral_eq_integral (hφ : IsSmoothTestFamilyIn U φ)
    (F : (Fin n → RealPlane) → ℂ) :
    productWeightedIntegral U φ F = ∫ x, (∏ i, ((φ i (x i) : ℝ) : ℂ)) * F x := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ U
  · simp only [Set.indicator_of_mem hx]
  · have hK : x ∉ Set.univ.pi fun i => tsupport (φ i) := fun hK => hx (hφ.2.2 hK)
    simp only [Set.indicator_of_notMem hx]
    rw [← Complex.ofReal_prod, prod_eq_zero_of_notMem_pi_tsupport hK]
    simp
theorem integrable_prod_mul (hφ : IsSmoothTestFamilyIn U φ) {F : (Fin n → RealPlane) → ℂ}
    (hF : ContinuousOn F U) :
    Integrable fun x => (∏ i, ((φ i (x i) : ℝ) : ℂ)) * F x := by
  have hprod : Continuous fun x : Fin n → RealPlane => ∏ i, ((φ i (x i) : ℝ) : ℂ) :=
    continuous_finsetProd _ fun i _ =>
      Complex.continuous_ofReal.comp ((hφ.1 i).continuous.comp (continuous_apply i))
  have hcont : ContinuousOn (fun x => (∏ i, ((φ i (x i) : ℝ) : ℂ)) * F x)
      (Set.univ.pi fun i => tsupport (φ i)) :=
    hprod.continuousOn.mul (hF.mono hφ.2.2)
  have hsupp : Function.support (fun x => (∏ i, ((φ i (x i) : ℝ) : ℂ)) * F x) ⊆
      Set.univ.pi fun i => tsupport (φ i) := by
    intro x hx
    by_contra hK
    apply hx
    show (∏ i, ((φ i (x i) : ℝ) : ℂ)) * F x = 0
    rw [← Complex.ofReal_prod, prod_eq_zero_of_notMem_pi_tsupport hK]
    simp
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  exact hcont.integrableOn_compact (isCompact_pi_tsupport hφ)
theorem exists_normed_bump_family (c : Fin n → RealPlane) {r : ℝ} (hr : 0 < r) :
    ∃ ψ : Fin n → RealPlane → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) ∧ (∀ i, HasCompactSupport (ψ i)) ∧
        (∀ i x, 0 ≤ ψ i x) ∧ (∀ i, ∫ x, ψ i x = 1) ∧
          ∀ i, tsupport (ψ i) = Metric.closedBall (c i) r := by
  have hex : ∀ i, ∃ b : ContDiffBump (c i), b.rOut = r := fun i =>
    ⟨⟨r / 2, r, half_pos hr, half_lt_self hr⟩, rfl⟩
  choose b hb using hex
  refine ⟨fun i => (b i).normed volume, fun i => (b i).contDiff_normed,
    fun i => (b i).hasCompactSupport_normed, fun i x => (b i).nonneg_normed x,
    fun i => (b i).integral_normed, fun i => ?_⟩
  rw [(b i).tsupport_normed_eq, hb i]
theorem eq_zero_of_forall_productWeightedIntegral_eq_zero (hU : IsOpen U)
    {G : (Fin n → RealPlane) → ℂ} (hG : ContinuousOn G U)
    (hvan : ∀ φ, IsSmoothTestFamilyIn U φ → productWeightedIntegral U φ G = 0)
    {c : Fin n → RealPlane} (hc : c ∈ U) : G c = 0 := by
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  have hat : ContinuousAt G c := hG.continuousAt (hU.mem_nhds hc)
  obtain ⟨ρ₁, hρ₁, hnearG⟩ := Metric.continuousAt_iff.mp hat ε hε
  obtain ⟨ρ₂, hρ₂, hballU⟩ := Metric.isOpen_iff.mp hU c hc
  obtain ⟨ρ, hρ, hρ₁le, hρ₂le⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₁ ∧ ρ ≤ ρ₂ :=
    ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨ψ, hsmooth, hcpt, hnn, hint, hts⟩ := exists_normed_bump_family c (half_pos hρ)
  have hclose : ∀ x ∈ Set.univ.pi (fun i => tsupport (ψ i)), dist x c < ρ := by
    intro x hx
    refine (dist_pi_lt_iff hρ).mpr fun i => ?_
    have hxi : x i ∈ tsupport (ψ i) := hx i (Set.mem_univ i)
    rw [hts i, Metric.mem_closedBall] at hxi
    linarith
  have hψ : IsSmoothTestFamilyIn U ψ :=
    ⟨hsmooth, hcpt,
      fun x hx => hballU (lt_of_lt_of_le (hclose x hx) hρ₂le)⟩
  have hmass : ∫ x : Fin n → RealPlane, ∏ i, ψ i (x i) = 1 := by
    rw [integral_fintype_prod_volume_eq_prod]
    exact Finset.prod_eq_one fun i _ => hint i
  have hmassInt : Integrable (fun x : Fin n → RealPlane => ∏ i, ψ i (x i)) :=
    (continuous_prod_apply hψ).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_pi_tsupport hψ)
        fun x hx => prod_eq_zero_of_notMem_pi_tsupport hx)
  have hconstInt : Integrable
      (fun x : Fin n → RealPlane => ((∏ i, ψ i (x i) : ℝ) : ℂ) * G c) :=
    hmassInt.ofReal.mul_const _
  have hrepr : G c = ∫ x, (((∏ i, ψ i (x i) : ℝ) : ℂ) * G c -
      (∏ i, ((ψ i (x i) : ℝ) : ℂ)) * G x) := by
    rw [integral_sub hconstInt (integrable_prod_mul hψ hG),
      ← productWeightedIntegral_eq_integral hψ,
      hvan ψ hψ, sub_zero, integral_mul_const, integral_complex_ofReal, hmass]
    simp
  have hpoint : ∀ x : Fin n → RealPlane,
      ‖((∏ i, ψ i (x i) : ℝ) : ℂ) * G c - (∏ i, ((ψ i (x i) : ℝ) : ℂ)) * G x‖ ≤
        (∏ i, ψ i (x i)) * ε := by
    intro x
    have hpos : 0 ≤ ∏ i, ψ i (x i) := Finset.prod_nonneg fun i _ => hnn i _
    rw [← Complex.ofReal_prod, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
    by_cases hx : x ∈ Set.univ.pi fun i => tsupport (ψ i)
    · refine mul_le_mul_of_nonneg_left ?_ hpos
      have hd := hnearG (lt_of_lt_of_le (hclose x hx) hρ₁le)
      rw [dist_eq_norm, norm_sub_rev] at hd
      exact hd.le
    · rw [prod_eq_zero_of_notMem_pi_tsupport hx]
      simp
  rw [hrepr]
  calc ‖∫ x, (((∏ i, ψ i (x i) : ℝ) : ℂ) * G c - (∏ i, ((ψ i (x i) : ℝ) : ℂ)) * G x)‖
      ≤ ∫ x, (∏ i, ψ i (x i)) * ε :=
        norm_integral_le_of_norm_le (hmassInt.mul_const ε) (Filter.Eventually.of_forall hpoint)
    _ = ε := by rw [integral_mul_const, hmass, one_mul]
theorem holds : Claim := by
  intro n _ U hU F hF
  refine ⟨fun h x hx => eq_zero_of_forall_productWeightedIntegral_eq_zero hU hF h hx,
    fun h x hx => ?_⟩
  have himc : ContinuousOn (fun x => (((F x).im : ℝ) : ℂ)) U :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn hF)
  refine Complex.ofReal_eq_zero.mp
    (eq_zero_of_forall_productWeightedIntegral_eq_zero hU himc (fun φ hφ => ?_) hx)
  have hzero := h φ hφ
  rw [productWeightedIntegral_eq_integral hφ] at hzero ⊢
  have hcomm : ∀ x, (∏ i, ((φ i (x i) : ℝ) : ℂ)) * (((F x).im : ℝ) : ℂ) =
      ((Complex.imCLM ((∏ i, ((φ i (x i) : ℝ) : ℂ)) * F x) : ℝ) : ℂ) := by
    intro x
    rw [← Complex.ofReal_prod, Complex.imCLM_apply, Complex.im_ofReal_mul, Complex.ofReal_mul]
  simp_rw [hcomm]
  rw [integral_complex_ofReal, Complex.imCLM.integral_comp_comm (integrable_prod_mul hφ hF),
    Complex.imCLM_apply, hzero, Complex.ofReal_zero]
end YangMills.Construction.RealPlane.DensityUniqueness
