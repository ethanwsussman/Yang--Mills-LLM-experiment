import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdStepAtMirrorFrames.CriticalAtAFieldWithAZeroFit
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
private theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : Quaternion ℝ)‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem re_expUnit_inv (w : imaginaryQuaternions) :
    (((expUnit w)⁻¹ : UnitQuaternion) : Quaternion ℝ).re = Real.cos ‖w‖ := by
  have hre : (w : Quaternion ℝ).re = 0 := w.2
  have hst : (((expUnit w)⁻¹ : UnitQuaternion) : Quaternion ℝ) = star ((expUnit w : UnitQuaternion) : Quaternion ℝ) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star]
  rw [hst, Quaternion.re_star]
  show (NormedSpace.exp (w : Quaternion ℝ)).re = _
  rw [Quaternion.exp_of_re_eq_zero _ hre]
  first
    | (simp [hre]; done)
    | (simp [hre]; rfl)
theorem criticalAtExactFit (hjet : FormCompositionJet)
    (hleast : minimalChainExistenceStatement) : CriticalAtExactFit := by
  classical
  intro F a S k W V ha hsm hval hmean
  set B := innerBonds S (k + 1) with hB
  set H := formComposition B (minimalAction a S (k + 1)) V with hH
  have hcd : ContDiffAt ℝ 3 H 0 := (hjet ℝ F (k + 1) B (minimalAction a S (k + 1)) V hsm).1
  have hfd : HasFDerivAt H (fderiv ℝ H 0) 0 :=
    (hcd.differentiableAt (by norm_num)).hasFDerivAt
  suffices hz : fderiv ℝ H 0 = 0 by rw [← hz]; exact hfd
  set ℓ := fderiv ℝ H 0 with hℓ
  ext A
  show ℓ A = 0
  choose ρ hρpos hρ using hmean
  have hline : HasDerivAt (fun τ : ℝ => H (τ • A)) (ℓ A) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => τ • A) A 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const A
    have hfd' : HasFDerivAt H ℓ ((0 : ℝ) • A) := by simpa using hfd
    exact hfd'.comp_hasDerivAt (0 : ℝ) h1
  set Cc : ℝ := a * ∑ c : ↥B, ρ c.1 * (‖A c‖ ^ 2 / 2) with hC
  have hH0 : H 0 = minimalAction a S k W := by
    rw [← hval]
    show minimalAction a S (k + 1) (leftTranslate (extendByZero (0 : ↥B → imaginaryQuaternions)) V) = _
    congr 1
    funext y i
    unfold leftTranslate extendByZero
    split_ifs
    · have : expUnit ((0 : ↥B → imaginaryQuaternions) ⟨(y, i), by assumption⟩) = 1 := by
        apply Subtype.ext
        show NormedSpace.exp ((0 : imaginaryQuaternions) : Quaternion ℝ) = 1
        simp
      rw [this, one_mul]
    · have : expUnit (0 : imaginaryQuaternions) = 1 := by
        apply Subtype.ext
        show NormedSpace.exp ((0 : imaginaryQuaternions) : Quaternion ℝ) = 1
        simp
      rw [this, one_mul]
  have hbound : ∀ τ : ℝ, H (τ • A) ≤ H 0 + Cc * τ ^ 2 := by
    intro τ
    rw [hH0]
    obtain ⟨hfit0, hnn, _, _⟩ := hleast F a S ha
    show minimalAction a S (k + 1) (leftTranslate (extendByZero (τ • A)) V) ≤ _
    have hle : minimalAction a S (k + 1) (leftTranslate (extendByZero (τ • A)) V) ≤
        minimalAction a S k W + a * ∑ c ∈ B, blockFit W (leftTranslate (extendByZero (τ • A)) V) c := by
      show (⨅ W' : F.GaugeField k, (minimalAction a S k W' +
        a * ∑ c ∈ innerBonds S (k + 1), blockFit W' (leftTranslate (extendByZero (τ • A)) V) c)) ≤ _
      apply ciInf_le ⟨0, ?_⟩ W
      rintro _ ⟨W', rfl⟩
      exact add_nonneg (hnn k W') (mul_nonneg ha (Finset.sum_nonneg fun c _ => hfit0 k W' _ c))
    refine hle.trans ?_
    have hfit : ∀ c : ↥B, blockFit W (leftTranslate (extendByZero (τ • A)) V) c.1 ≤
        ρ c.1 * (‖A c‖ ^ 2 / 2) * τ ^ 2 := by
      rintro ⟨⟨y, i⟩, hc⟩
      have hext : extendByZero (τ • A) y i = τ • A ⟨(y, i), hc⟩ := by
        unfold extendByZero
        rw [dif_pos hc]
        rfl
      unfold blockFit
      dsimp only
      rw [hρ (y, i)]
      dsimp only
      have h1 : ‖ρ (y, i) • ((V y i : UnitQuaternion) : Quaternion ℝ)‖ = ρ (y, i) := by
        rw [norm_smul, norm_unitQuaternion, mul_one, Real.norm_eq_abs, abs_of_pos (hρpos _)]
      have h2 : (ρ (y, i) • ((V y i : UnitQuaternion) : Quaternion ℝ) *
          (((leftTranslate (extendByZero (τ • A)) V y i)⁻¹ : UnitQuaternion) : Quaternion ℝ)).re =
          ρ (y, i) * Real.cos ‖τ • A ⟨(y, i), hc⟩‖ := by
        have he : (leftTranslate (extendByZero (τ • A)) V y i)⁻¹ =
            (V y i)⁻¹ * (expUnit (τ • A ⟨(y, i), hc⟩))⁻¹ := by
          unfold leftTranslate
          rw [hext, mul_inv_rev]
        rw [he, smul_mul_assoc]
        have h3 : ((V y i : UnitQuaternion) : Quaternion ℝ) *
            (((V y i)⁻¹ * (expUnit (τ • A ⟨(y, i), hc⟩))⁻¹ : UnitQuaternion) : Quaternion ℝ) =
            (((expUnit (τ • A ⟨(y, i), hc⟩))⁻¹ : UnitQuaternion) : Quaternion ℝ) := by
          show ((V y i * ((V y i)⁻¹ * (expUnit (τ • A ⟨(y, i), hc⟩))⁻¹) : UnitQuaternion) : Quaternion ℝ) = _
          rw [mul_inv_cancel_left]
        rw [h3]
        simp [re_expUnit_inv]
      rw [h1, h2]
      have hnorm : ‖τ • A ⟨(y, i), hc⟩‖ = |τ| * ‖A ⟨(y, i), hc⟩‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      have hcos := Real.one_sub_sq_div_two_le_cos (x := ‖τ • A ⟨(y, i), hc⟩‖)
      rw [hnorm, mul_pow, sq_abs] at hcos
      have hr := (hρpos (y, i)).le
      rw [hnorm]
      nlinarith [mul_le_mul_of_nonneg_left hcos hr]
    have hsum : ∑ c ∈ B, blockFit W (leftTranslate (extendByZero (τ • A)) V) c ≤
        ∑ c : ↥B, ρ c.1 * (‖A c‖ ^ 2 / 2) * τ ^ 2 := by
      rw [← Finset.sum_coe_sort B]
      exact Finset.sum_le_sum fun c _ => hfit c
    have := mul_le_mul_of_nonneg_left hsum ha
    rw [hC, ← Finset.sum_mul] at *
    nlinarith
  have hmax : IsLocalMax (fun τ : ℝ => H (τ • A) - Cc * τ ^ 2) 0 := by
    filter_upwards with τ
    have := hbound τ
    simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero]
    linarith
  have hd : HasDerivAt (fun τ : ℝ => H (τ • A) - Cc * τ ^ 2) (ℓ A - 0) 0 := by
    apply hline.sub
    have := ((hasDerivAt_id (0 : ℝ)).pow 2).const_mul Cc
    simpa using this
  have := hmax.hasDerivAt_eq_zero hd
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
