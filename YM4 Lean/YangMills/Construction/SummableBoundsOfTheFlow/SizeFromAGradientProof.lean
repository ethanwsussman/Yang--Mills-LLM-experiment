import YangMills.Construction.SummableBoundsOfTheFlow.SizeFromAGradient
import YangMills.Construction.SummableBoundsOfTheFlow.SizeFromSquareBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
theorem localSizeOfGradientBound_of_quadraticBounds (hSz : localSizeOfQuadraticBoundsStatement) :
    localSizeOfGradientBoundStatement := by
  intro ι _ _ ρ x lam κ W C g d Φ p dZ T hρ hx hlam hκ hW hg hp hd hconv hWd hWz hC hgrad
  have hx0 : 0 < x := by linarith
  set r := Real.sqrt x with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hx0
  have hrr : r * r = x := Real.mul_self_sqrt hx0.le
  have hpow : x ^ (-(1 / 2 : ℝ)) = r⁻¹ := by
    rw [Real.rpow_neg hx0.le, hr, Real.sqrt_eq_rpow]
  set u : ι → ℝ := fun b => Real.exp (-(2 * κ * dZ b)) with hu
  have hu0 : ∀ b, 0 ≤ u b := fun b => (Real.exp_pos _).le
  rw [hpow]
  have hh : 0 ≤ (W + 1) * g * r⁻¹ := by positivity
  refine hSz ι ρ x lam κ W W C ((W + 1) * g * r⁻¹) (T 0) d Φ p dZ u T hρ hx hlam hκ hW hW hh hp hd
    hconv hWd hu0 hWz hC ?_ ?_
  · intro η hη
    have hall : ∀ ζ : BondField ι, (∀ b, ‖ζ b‖ < ρ) → ∀ (b : ι) (e : BondVector),
        |fderiv ℝ T ζ (bondVariation b e)| ≤ g * u b * ‖e‖ := by
      intro ζ hζ b e
      by_cases he : e = 0
      · subst he
        simp [bondVariation]
      · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
        have hunit : ‖‖e‖⁻¹ • e‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
        have hscale : bondVariation b e = ‖e‖ • bondVariation b (‖e‖⁻¹ • e) := by
          simp only [bondVariation]
          rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
        have hbound := hgrad ζ b _ hζ hunit
        rw [hscale, map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (norm_nonneg _), mul_comm]
        exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    have hball : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(t • η) b‖ < ρ := by
      intro t ht b
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      have := hη b
      nlinarith [norm_nonneg (η b), ht.2, ht.1]
    have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => T (t • η)) (fderiv ℝ T (t • η) η) t := by
      intro t ht
      have hdiff : DifferentiableAt ℝ T (t • η) := (hC _ (hball t ht)).differentiableAt (by simp)
      have hline : HasDerivAt (fun t : ℝ => t • η) η t := by
        simpa using (hasDerivAt_id t).smul_const η
      exact hdiff.hasFDerivAt.comp_hasDerivAt t hline
    have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖deriv (fun t : ℝ => T (t • η)) t‖ ≤ ∑ b, g * u b * ‖η b‖ := by
      intro t ht
      rw [(hder t ht).deriv, Real.norm_eq_abs]
      have hdecomp : ∑ b, bondVariation b (η b) = η := Finset.univ_sum_single η
      have hsplit : fderiv ℝ T (t • η) η = ∑ b, fderiv ℝ T (t • η) (bondVariation b (η b)) := by
        have hmap := map_sum (fderiv ℝ T (t • η)) (fun b => bondVariation b (η b)) Finset.univ
        rw [← hmap, hdecomp]
      rw [hsplit]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun b _ => hall _ (hball t ht) b _)
    have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hder t ht).differentiableAt) hbd (Set.left_mem_Icc.2 zero_le_one)
      (Set.right_mem_Icc.2 zero_le_one)
    simp only [one_smul, zero_smul, sub_zero, norm_one, mul_one, Real.norm_eq_abs] at hmvt
    refine hmvt.trans ?_
    have hterm : ∀ b, u b * ‖η b‖ ≤ (2 * r)⁻¹ * (x * (u b * ‖η b‖ ^ 2) + u b) := by
      intro b
      have hamgm : 2 * r * ‖η b‖ ≤ x * ‖η b‖ ^ 2 + 1 := by
        nlinarith [sq_nonneg (r * ‖η b‖ - 1)]
      have hdiv : ‖η b‖ ≤ (2 * r)⁻¹ * (x * ‖η b‖ ^ 2 + 1) := by
        rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
        linarith
      have := mul_le_mul_of_nonneg_left hdiv (hu0 b)
      calc _ ≤ _ := this
        _ = _ := by ring
    set Sq := ∑ b, u b * ‖η b‖ ^ 2 with hSq
    have hS0 : 0 ≤ Sq := Finset.sum_nonneg fun b _ => mul_nonneg (hu0 b) (sq_nonneg _)
    have hsum : ∑ b, u b * ‖η b‖ ≤ (2 * r)⁻¹ * (x * Sq + W) := by
      refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    have hfactor : ∑ b, g * u b * ‖η b‖ = g * ∑ b, u b * ‖η b‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hfactor]
    have hxs : 0 ≤ x * Sq := mul_nonneg hx0.le hS0
    have hlin : x * Sq + W ≤ (W + 1) * (x * Sq + 1) := by nlinarith
    have hinv : (2 * r)⁻¹ = 2⁻¹ * r⁻¹ := mul_inv _ _
    have hm : 0 ≤ x * Sq + 1 := by linarith
    calc g * ∑ b, u b * ‖η b‖ ≤ g * ((2 * r)⁻¹ * ((W + 1) * (x * Sq + 1))) :=
          mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hlin (by positivity))) hg
      _ = 2⁻¹ * ((W + 1) * g * r⁻¹ * (x * Sq + 1)) := by rw [hinv]; ring
      _ ≤ (W + 1) * g * r⁻¹ * (x * Sq + 1) := by
          have : 0 ≤ (W + 1) * g * r⁻¹ * (x * Sq + 1) := by positivity
          linarith
  · intro η b hη
    have hS0 : 0 ≤ ∑ b, u b * ‖η b‖ ^ 2 :=
      Finset.sum_nonneg fun b _ => mul_nonneg (hu0 b) (sq_nonneg _)
    have hcancel : r * ((W + 1) * g * r⁻¹) = (W + 1) * g := by
      field_simp
    rw [hcancel]
    have hm : 1 ≤ x * ∑ b, u b * ‖η b‖ ^ 2 + 1 := by nlinarith
    have hB : 0 ≤ (W + 1) * g * Real.exp (-(2 * κ * dZ b)) * (x * ∑ b, u b * ‖η b‖ ^ 2 + 1) := by
      positivity
    unfold bondGradNorm
    refine ContinuousLinearMap.opNorm_le_of_unit_norm hB fun e he => ?_
    have hbound := hgrad η b e hη he
    have happly : ((fderiv ℝ T η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)) e =
        fderiv ℝ T η (bondVariation b e) := rfl
    rw [happly, Real.norm_eq_abs]
    refine hbound.trans ?_
    have hE := (Real.exp_pos (-(2 * κ * dZ b))).le
    have hgW : g * Real.exp (-(2 * κ * dZ b)) ≤ (W + 1) * g * Real.exp (-(2 * κ * dZ b)) := by
      have : g ≤ (W + 1) * g := by nlinarith
      exact mul_le_mul_of_nonneg_right this hE
    refine hgW.trans ?_
    have hnn : 0 ≤ (W + 1) * g * Real.exp (-(2 * κ * dZ b)) := by positivity
    exact le_mul_of_one_le_right hnn hm
end Interpolation
end YangMills.Construction
end
