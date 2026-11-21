import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenInValueProofForm
import YangMills.Construction.ColdStepAtMirrorFrames.SegmentOfConvexExponents
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace SegmentInterpolation
section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ m κ : ℝ} {d : ι → ι → ℝ}
theorem secondDerivAlong_segmentInterpolant {F G : BondField ι → ℝ} (hF : ContDiff ℝ 3 F)
    (hG : ContDiff ℝ 3 G) (t : ℝ) (η u w : BondField ι) :
    secondDerivAlong (segmentInterpolant F G t) η u w =
      t * secondDerivAlong G η u w + (1 - t) * secondDerivAlong F η u w := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.secondDeriv_segment <;> assumption
theorem contDiff_segmentInterpolant {F G : BondField ι → ℝ} (hF : ContDiff ℝ 3 F) (hG : ContDiff ℝ 3 G)
    (t : ℝ) : ContDiff ℝ 3 (segmentInterpolant F G t) :=
  (contDiff_const.mul hG).add (contDiff_const.mul hF)
theorem segmentInterpolant_isConvexWithSmallGradient {F G : BondField ι → ℝ} (hm : 0 < m)
    (hF : IsConvexWithSmallGradient ρ m κ d F) (hG : IsConvexWithSmallGradient ρ m κ d G) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsConvexWithSmallGradient ρ m κ d (segmentInterpolant F G t) := by
  obtain ⟨⟨KF, hKF⟩, gF⟩ := hF
  obtain ⟨⟨KG, hKG⟩, gG⟩ := hG
  have ht1' : 0 ≤ 1 - t := by linarith
  refine ⟨⟨fun b b' => t * KG b b' + (1 - t) * KF b b', ?_⟩, ?_⟩
  · refine ⟨contDiff_segmentInterpolant hKF.smooth hKG.smooth t, ?_, ?_, ?_, ?_⟩
    · intro η hη u
      rw [secondDerivAlong_segmentInterpolant hKF.smooth hKG.smooth]
      have eF := hKF.floor η hη u
      have eG := hKG.floor η hη u
      nlinarith [mul_le_mul_of_nonneg_left eG ht0, mul_le_mul_of_nonneg_left eF ht1']
    · intro η hη b b' x y
      rw [secondDerivAlong_segmentInterpolant hKF.smooth hKG.smooth]
      have eF := hKF.kernel η hη b b' x y
      have eG := hKG.kernel η hη b b' x y
      calc _ ≤ |t * secondDerivAlong G η (bondVariation b x) (bondVariation b' y)| +
            |(1 - t) * secondDerivAlong F η (bondVariation b x) (bondVariation b' y)| := abs_add_le _ _
        _ = t * |secondDerivAlong G η (bondVariation b x) (bondVariation b' y)| +
            (1 - t) * |secondDerivAlong F η (bondVariation b x) (bondVariation b' y)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht1']
        _ ≤ t * (KG b b' * ‖x‖ * ‖y‖) + (1 - t) * (KF b b' * ‖x‖ * ‖y‖) := by gcongr
        _ = _ := by ring
    · intro b b'
      simp only [hKF.symm b b', hKG.symm b b']
    · intro b
      have eF := hKF.standingConstraints b
      have eG := hKG.standingConstraints b
      have : ∑ b', (t * KG b b' + (1 - t) * KF b b') * (Real.exp (2 * κ * d b b') - 1) =
          t * ∑ b', KG b b' * (Real.exp (2 * κ * d b b') - 1) +
            (1 - t) * ∑ b', KF b b' * (Real.exp (2 * κ * d b b') - 1) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left eG ht0, mul_le_mul_of_nonneg_left eF ht1']
  · intro b x
    have hFd : Differentiable ℝ F := hKF.smooth.differentiable (by simp)
    have hGd : Differentiable ℝ G := hKG.smooth.differentiable (by simp)
    have : bondPartialDeriv (segmentInterpolant F G t) b 0 x =
        t * bondPartialDeriv G b 0 x + (1 - t) * bondPartialDeriv F b 0 x := by
      unfold bondPartialDeriv
      have : HasFDerivAt (segmentInterpolant F G t) (t • fderiv ℝ G 0 + (1 - t) • fderiv ℝ F 0) 0 :=
        ((hGd 0).hasFDerivAt.const_mul t).add ((hFd 0).hasFDerivAt.const_mul (1 - t))
      rw [this.fderiv]
      simp
    rw [this]
    calc _ ≤ |t * bondPartialDeriv G b 0 x| + |(1 - t) * bondPartialDeriv F b 0 x| := abs_add_le _ _
      _ = t * |bondPartialDeriv G b 0 x| + (1 - t) * |bondPartialDeriv F b 0 x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht1']
      _ ≤ t * (Real.sqrt m * ‖x‖) + (1 - t) * (Real.sqrt m * ‖x‖) := by
        gcongr
        · exact gG b x
        · exact gF b x
      _ = _ := by ring
theorem fderiv_quadratic (c : ℝ) (η u : BondField ι) :
    fderiv ℝ (fun ζ : BondField ι => c * ∑ b, ‖ζ b‖ ^ 2) η u = 2 * c * ∑ b, ⟪η b, u b⟫ := by
  have hterm : ∀ b, HasFDerivAt (fun ζ : BondField ι => ‖ζ b‖ ^ 2)
      ((2 : ℝ) • (innerSL ℝ (η b)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)) η := fun b => by
    have := (hasStrictFDerivAt_norm_sq (η b)).hasFDerivAt.comp η
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
    refine HasFDerivAt.congr_fderiv this ?_
    ext w
    simp
  have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) fun b _ => hterm b).const_mul c
  rw [hsum.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring
theorem secondDerivAlong_quadratic (c : ℝ) (η u w : BondField ι) :
    secondDerivAlong (fun ζ : BondField ι => c * ∑ b, ‖ζ b‖ ^ 2) η u w = 2 * c * ∑ b, ⟪u b, w b⟫ := by
  unfold secondDerivAlong
  set L : BondField ι →L[ℝ] ℝ := (2 * c) • ∑ b, (innerSL ℝ (u b)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b) with hLdef
  have hL : ∀ z, L z = 2 * c * ∑ b, ⟪u b, z b⟫ := fun z => by
    simp [hLdef, ContinuousLinearMap.sum_apply]
  have hfun : (fun ζ => fderiv ℝ (fun ζ : BondField ι => c * ∑ b, ‖ζ b‖ ^ 2) ζ u) = fun ζ => L ζ := by
    funext ζ
    rw [fderiv_quadratic, hL]
    congr 1
    exact Finset.sum_congr rfl fun b _ => real_inner_comm _ _
  rw [hfun, ContinuousLinearMap.fderiv, hL]
theorem quadratic_isConvexWithSmallGradient {c : ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hc : m ≤ c)
    (hd : ∀ b, d b b = 0) :
    IsConvexWithSmallGradient ρ m κ d (fun η => c * ∑ b, ‖η b‖ ^ 2) := by
  have hc0 : 0 ≤ c := hm.le.trans hc
  refine ⟨⟨fun b b' => if b = b' then 2 * c else 0, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · apply contDiff_const.mul
    apply ContDiff.sum
    intro b _
    exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ BondVector b)
  · intro η _ u
    rw [secondDerivAlong_quadratic]
    have hinner : ∑ b, ⟪u b, u b⟫ = ∑ b, ‖u b‖ ^ 2 :=
      Finset.sum_congr rfl fun b _ => real_inner_self_eq_norm_sq _
    have hnonneg : 0 ≤ ∑ b, ‖u b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    rw [hinner]
    nlinarith [mul_le_mul_of_nonneg_right hc hnonneg]
  · intro η _ b b' x y
    rw [secondDerivAlong_quadratic]
    by_cases hbb : b = b'
    · subst hbb
      rw [if_pos rfl, Finset.sum_eq_single b]
      · simp only [bondVariation, Pi.single_eq_same]
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 2 * c)]
        have := abs_real_inner_le_norm x y
        calc 2 * c * |⟪x, y⟫| ≤ 2 * c * (‖x‖ * ‖y‖) := by gcongr
          _ = _ := by ring
      · intro e _ he
        simp [bondVariation, he]
      · intro h
        exact absurd (Finset.mem_univ b) h
    · rw [if_neg hbb]
      have : ∑ e, ⟪bondVariation b x e, bondVariation b' y e⟫ = 0 := by
        apply Finset.sum_eq_zero
        intro e _
        by_cases heb : e = b
        · subst heb
          simp [bondVariation, hbb]
        · simp [bondVariation, heb]
      rw [this]
      simp
  · intro b b'
    simp only [eq_comm]
  · intro b
    have : ∀ b', (if b = b' then 2 * c else 0) * (Real.exp (2 * κ * d b b') - 1) = 0 := fun b' => by
      by_cases hbb : b = b'
      · subst hbb
        simp [hd]
      · simp [hbb]
    simp only [this, Finset.sum_const_zero]
    exact hm.le
  · intro b x
    unfold bondPartialDeriv
    rw [fderiv_quadratic]
    simp
    positivity
end
end SegmentInterpolation
open SegmentInterpolation in
theorem convexSmallGradientClassSegment_proof : ConvexSmallGradientClassSegment := by
  intro ι _ _ ρ m κ c d hρ hm hc hd
  exact ⟨fun F G t hF hG ht0 ht1 => segmentInterpolant_isConvexWithSmallGradient hm hF hG ht0 ht1,
    quadratic_isConvexWithSmallGradient hρ hm hc hd⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
