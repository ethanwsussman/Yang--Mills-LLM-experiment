import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongAFlowProof
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponentialProof
import YangMills.Construction.ColdStepAtMirrorFrames.PlaquetteOfACutFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames.SmallUnits
open YangMills.Construction.BlockAverages
open YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
def imagPart (q : ℍ[ℝ]) : imaginaryQuaternions := ⟨q.im, by show (q.im).re = 0; simp⟩
def logUnit (g : UnitQuaternion) : imaginaryQuaternions :=
  (Real.arccos (g : ℍ[ℝ]).re / ‖imagPart g‖) • imagPart g
theorem norm_sq_eq_re_sq_add_norm_imagPart_sq (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + ‖imagPart q‖ ^ 2 := by
  have hq : ‖imagPart q‖ = ‖q.im‖ := rfl
  rw [hq, sq ‖q‖, sq ‖q.im‖, ← Quaternion.normSq_eq_norm_mul_self, ← Quaternion.normSq_eq_norm_mul_self,
    Quaternion.normSq_def', Quaternion.normSq_def']
  simp
  ring
theorem re_sq_add_norm_imagPart_sq (g : UnitQuaternion) : (g : ℍ[ℝ]).re ^ 2 + ‖imagPart g‖ ^ 2 = 1 := by
  rw [← norm_sq_eq_re_sq_add_norm_imagPart_sq, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion]
  norm_num
theorem distFromOne_sq (g : UnitQuaternion) : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g ^ 2 = 2 - 2 * (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
theorem re_le_one (g : UnitQuaternion) : (g : ℍ[ℝ]).re ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.re_coe_le_one <;> assumption
theorem neg_one_le_re (g : UnitQuaternion) : -1 ≤ (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.BlockAverages.neg_one_le_re_coe <;> assumption
theorem sin_arccos_re (g : UnitQuaternion) : Real.sin (Real.arccos (g : ℍ[ℝ]).re) = ‖imagPart g‖ := by
  rw [Real.sin_arccos]
  have := re_sq_add_norm_imagPart_sq g
  have hg : 1 - (g : ℍ[ℝ]).re ^ 2 = ‖imagPart g‖ ^ 2 := by linarith
  rw [hg, Real.sqrt_sq (norm_nonneg _)]
theorem norm_logUnit (g : UnitQuaternion) (h : ‖imagPart g‖ ≠ 0) : ‖logUnit g‖ = Real.arccos (g : ℍ[ℝ]).re := by
  unfold logUnit
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.arccos_nonneg _) (norm_nonneg _)),
    div_mul_cancel₀ _ h]
theorem expUnit_logUnit (g : UnitQuaternion) (h : 0 < (g : ℍ[ℝ]).re) : expUnit (logUnit g) = g := by
  apply Subtype.ext
  show NormedSpace.exp ((logUnit g : imaginaryQuaternions) : ℍ[ℝ]) = (g : ℍ[ℝ])
  by_cases hv : ‖imagPart g‖ = 0
  · have hv' : imagPart g = 0 := norm_eq_zero.1 hv
    have hu := re_sq_add_norm_imagPart_sq g
    rw [hv] at hu
    have hs : (g : ℍ[ℝ]).re = 1 := by nlinarith
    have him : (g : ℍ[ℝ]).im = 0 := congrArg Subtype.val hv'
    have hq : (g : ℍ[ℝ]) = 1 := by
      rw [← Quaternion.re_add_im (g : ℍ[ℝ]), him, hs]
      simp
    have hl : logUnit g = 0 := by
      unfold logUnit
      rw [hv']
      simp
    rw [hl, hq]
    simp
  · rw [exp_imaginary_eq (logUnit g)]
    have hn : ‖((logUnit g : imaginaryQuaternions) : ℍ[ℝ])‖ = Real.arccos (g : ℍ[ℝ]).re := norm_logUnit g hv
    rw [hn, Real.cos_arccos (by have := neg_one_le_re g; linarith) (re_le_one g), sin_arccos_re]
    have hθ : Real.arccos (g : ℍ[ℝ]).re ≠ 0 := by
      intro h0
      have := sin_arccos_re g
      rw [h0, Real.sin_zero] at this
      exact hv this.symm
    have hl : ((logUnit g : imaginaryQuaternions) : ℍ[ℝ]) = (Real.arccos (g : ℍ[ℝ]).re / ‖imagPart g‖) • (g : ℍ[ℝ]).im := rfl
    rw [hl, smul_smul]
    have : ‖imagPart g‖ / Real.arccos (g : ℍ[ℝ]).re * (Real.arccos (g : ℍ[ℝ]).re / ‖imagPart g‖) = 1 := by
      field_simp
    rw [this, one_smul]
    exact Quaternion.re_add_im _
theorem norm_logUnit_le (g : UnitQuaternion) : ‖logUnit g‖ ≤ 2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g := by
  by_cases hv : ‖imagPart g‖ = 0
  · have hv' : imagPart g = 0 := norm_eq_zero.1 hv
    have hl : logUnit g = 0 := by
      unfold logUnit
      rw [hv']
      simp
    rw [hl, norm_zero]
    exact mul_nonneg (by norm_num) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_nonneg g)
  · rw [norm_logUnit g hv]
    set θ := Real.arccos (g : ℍ[ℝ]).re with hθ
    have h0 : 0 ≤ θ := Real.arccos_nonneg _
    have hπ : θ ≤ Real.pi := Real.arccos_le_pi _
    have hc : Real.cos θ = (g : ℍ[ℝ]).re := Real.cos_arccos (neg_one_le_re g) (re_le_one g)
    have hs : 2 / Real.pi * (θ / 2) ≤ Real.sin (θ / 2) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have hg : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
      rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallUnits.distFromOne_sq, ← hc]
      have := Real.cos_sq' (θ / 2)
      have h2 : Real.cos θ = Real.cos (2 * (θ / 2)) := by congr 1; ring
      rw [h2, Real.cos_two_mul]
      nlinarith
    have hs0 : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hg' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g = 2 * Real.sin (θ / 2) :=
      (sq_eq_sq₀ (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_nonneg g) (by positivity)).1 hg
    rw [hg']
    have hp := Real.pi_pos
    have hp4 : Real.pi ≤ 4 := Real.pi_le_four
    have : θ / Real.pi ≤ Real.sin (θ / 2) := by
      calc θ / Real.pi = 2 / Real.pi * (θ / 2) := by ring
        _ ≤ _ := hs
    have h4 : θ / 4 ≤ θ / Real.pi := div_le_div_of_nonneg_left h0 hp hp4
    linarith
theorem norm_expUnit_sub_one_sub_le (x : imaginaryQuaternions) (hx : ‖x‖ ≤ 1) :
    ‖((expUnit x : UnitQuaternion) : ℍ[ℝ]) - 1 - (x : ℍ[ℝ])‖ ≤ ‖x‖ ^ 2 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FourPlaquette.norm_expUnit_sub_one_sub_le_sq <;> assumption
theorem expUnit_neg (r : imaginaryQuaternions) : expUnit (-r) = (expUnit r)⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.expUnit_neg <;> assumption
theorem norm_mul_four_sub_sum_le (g₁ g₂ g₃ g₄ : UnitQuaternion) (M : ℝ) (h₁ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g₁ ≤ M)
    (h₂ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g₂ ≤ M) (h₃ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g₃ ≤ M) (h₄ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g₄ ≤ M) :
    ‖((g₁ * g₂ * g₃ * g₄ : UnitQuaternion) : ℍ[ℝ]) - 1 -
      (((g₁ : ℍ[ℝ]) - 1) + ((g₂ : ℍ[ℝ]) - 1) + ((g₃ : ℍ[ℝ]) - 1) + ((g₄ : ℍ[ℝ]) - 1))‖ ≤ 6 * M ^ 2 := by
  have n₁ := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_nonneg g₁
  have hsplit : ((g₁ * g₂ * g₃ * g₄ : UnitQuaternion) : ℍ[ℝ]) - 1 -
      (((g₁ : ℍ[ℝ]) - 1) + ((g₂ : ℍ[ℝ]) - 1) + ((g₃ : ℍ[ℝ]) - 1) + ((g₄ : ℍ[ℝ]) - 1)) =
      ((g₁ : ℍ[ℝ]) - 1) * (((g₂ * g₃ * g₄ : UnitQuaternion) : ℍ[ℝ]) - 1) +
        ((g₂ : ℍ[ℝ]) - 1) * (((g₃ * g₄ : UnitQuaternion) : ℍ[ℝ]) - 1) + ((g₃ : ℍ[ℝ]) - 1) * ((g₄ : ℍ[ℝ]) - 1) := by
    simp only [Submonoid.coe_mul]
    noncomm_ring
  rw [hsplit]
  have b3 : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (g₂ * g₃ * g₄) ≤ 3 * M := by
    have := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul (g₂ * g₃) g₄
    have := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul g₂ g₃
    linarith
  have b2 : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (g₃ * g₄) ≤ 2 * M := by
    have := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul g₃ g₄
    linarith
  have hM : 0 ≤ M := n₁.trans h₁
  have t1 : ‖((g₁ : ℍ[ℝ]) - 1) * (((g₂ * g₃ * g₄ : UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤ M * (3 * M) := by
    rw [norm_mul]
    exact mul_le_mul h₁ b3 (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_nonneg _) hM
  have t2 : ‖((g₂ : ℍ[ℝ]) - 1) * (((g₃ * g₄ : UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤ M * (2 * M) := by
    rw [norm_mul]
    exact mul_le_mul h₂ b2 (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_nonneg _) hM
  have t3 : ‖((g₃ : ℍ[ℝ]) - 1) * ((g₄ : ℍ[ℝ]) - 1)‖ ≤ M * M := by
    rw [norm_mul]
    exact mul_le_mul h₃ h₄ (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_nonneg _) hM
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (((g₁ : ℍ[ℝ]) - 1) * (((g₂ * g₃ * g₄ : UnitQuaternion) : ℍ[ℝ]) - 1))
    (((g₂ : ℍ[ℝ]) - 1) * (((g₃ * g₄ : UnitQuaternion) : ℍ[ℝ]) - 1))
  nlinarith
def scaledPlaquette (a₁ a₂ a₃ a₄ : imaginaryQuaternions) (t₁ t₂ t₃ t₄ : ℝ) : UnitQuaternion :=
  expUnit (t₁ • a₁) * expUnit (t₂ • a₂) * (expUnit (t₃ • a₃))⁻¹ * (expUnit (t₄ • a₄))⁻¹
theorem norm_scaledPlaquette_sub_linear_le (a₁ a₂ a₃ a₄ : imaginaryQuaternions) (t₁ t₂ t₃ t₄ M : ℝ) (hM : M ≤ 1)
    (h₁ : ‖a₁‖ ≤ M) (h₂ : ‖a₂‖ ≤ M) (h₃ : ‖a₃‖ ≤ M) (h₄ : ‖a₄‖ ≤ M) (ht₁ : |t₁| ≤ 1) (ht₂ : |t₂| ≤ 1)
    (ht₃ : |t₃| ≤ 1) (ht₄ : |t₄| ≤ 1) :
    ‖((scaledPlaquette a₁ a₂ a₃ a₄ t₁ t₂ t₃ t₄ : UnitQuaternion) : ℍ[ℝ]) - 1 -
      (t₁ • (a₁ : ℍ[ℝ]) + t₂ • (a₂ : ℍ[ℝ]) - t₃ • (a₃ : ℍ[ℝ]) - t₄ • (a₄ : ℍ[ℝ]))‖ ≤ 10 * M ^ 2 := by
  have sm : ∀ (t : ℝ) (a : imaginaryQuaternions), |t| ≤ 1 → ‖a‖ ≤ M → ‖t • a‖ ≤ M := fun t a ht ha => by
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg a, abs_nonneg t]
  have ex : ∀ (t : ℝ) (a : imaginaryQuaternions), |t| ≤ 1 → ‖a‖ ≤ M →
      ‖((expUnit (t • a) : UnitQuaternion) : ℍ[ℝ]) - 1 - t • (a : ℍ[ℝ])‖ ≤ M ^ 2 := fun t a ht ha => by
    have h := norm_expUnit_sub_one_sub_le (t • a) ((sm t a ht ha).trans hM)
    have hc : ((t • a : imaginaryQuaternions) : ℍ[ℝ]) = t • (a : ℍ[ℝ]) := rfl
    rw [hc] at h
    refine h.trans (pow_le_pow_left₀ (norm_nonneg _) (sm t a ht ha) 2)
  have ex' : ∀ (t : ℝ) (a : imaginaryQuaternions), |t| ≤ 1 → ‖a‖ ≤ M →
      ‖(((expUnit (t • a))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 + t • (a : ℍ[ℝ])‖ ≤ M ^ 2 := fun t a ht ha => by
    have h := ex (-t) a (by simpa using ht) ha
    have hneg : expUnit ((-t) • a) = (expUnit (t • a))⁻¹ := by
      have h0 : (-t) • a = -(t • a) := by
        apply Subtype.ext
        show (-t) • (a : ℍ[ℝ]) = -(t • (a : ℍ[ℝ]))
        exact neg_smul t (a : ℍ[ℝ])
      rw [h0, expUnit_neg]
    rw [hneg] at h
    have h2 : (((expUnit (t • a))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 - (-t) • (a : ℍ[ℝ]) =
        (((expUnit (t • a))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 + t • (a : ℍ[ℝ]) := by
      rw [neg_smul, sub_neg_eq_add]
    rwa [h2] at h
  have gp : ∀ (t : ℝ) (a : imaginaryQuaternions), |t| ≤ 1 → ‖a‖ ≤ M → _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (expUnit (t • a)) ≤ M :=
    fun t a ht ha => (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le _).trans (sm t a ht ha)
  have key := norm_mul_four_sub_sum_le (expUnit (t₁ • a₁)) (expUnit (t₂ • a₂)) (expUnit (t₃ • a₃))⁻¹
    (expUnit (t₄ • a₄))⁻¹ M (gp _ _ ht₁ h₁) (gp _ _ ht₂ h₂) (by rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_inv]; exact gp _ _ ht₃ h₃)
    (by rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_inv]; exact gp _ _ ht₄ h₄)
  have hsplit : ((scaledPlaquette a₁ a₂ a₃ a₄ t₁ t₂ t₃ t₄ : UnitQuaternion) : ℍ[ℝ]) - 1 -
      (t₁ • (a₁ : ℍ[ℝ]) + t₂ • (a₂ : ℍ[ℝ]) - t₃ • (a₃ : ℍ[ℝ]) - t₄ • (a₄ : ℍ[ℝ])) =
      (((expUnit (t₁ • a₁) * expUnit (t₂ • a₂) * (expUnit (t₃ • a₃))⁻¹ * (expUnit (t₄ • a₄))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 -
        ((((expUnit (t₁ • a₁) : UnitQuaternion) : ℍ[ℝ]) - 1) + (((expUnit (t₂ • a₂) : UnitQuaternion) : ℍ[ℝ]) - 1) +
          ((((expUnit (t₃ • a₃))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) + ((((expUnit (t₄ • a₄))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1))) +
        (((expUnit (t₁ • a₁) : UnitQuaternion) : ℍ[ℝ]) - 1 - t₁ • (a₁ : ℍ[ℝ])) +
        (((expUnit (t₂ • a₂) : UnitQuaternion) : ℍ[ℝ]) - 1 - t₂ • (a₂ : ℍ[ℝ])) +
        ((((expUnit (t₃ • a₃))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 + t₃ • (a₃ : ℍ[ℝ])) +
        ((((expUnit (t₄ • a₄))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 + t₄ • (a₄ : ℍ[ℝ])) := by
    unfold scaledPlaquette
    abel
  rw [hsplit]
  have b1 := ex t₁ a₁ ht₁ h₁
  have b2 := ex t₂ a₂ ht₂ h₂
  have b3 := ex' t₃ a₃ ht₃ h₃
  have b4 := ex' t₄ a₄ ht₄ h₄
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_add_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _) _).trans ?_
  nlinarith
theorem expUnit_add_smul (s t : ℝ) (D : imaginaryQuaternions) :
    expUnit ((s + t) • D) = expUnit (s • D) * expUnit (t • D) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlowDerivative.expUnit_add_smul <;> assumption
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
end YangMills.Construction.ColdStepAtMirrorFrames.SmallUnits
end
