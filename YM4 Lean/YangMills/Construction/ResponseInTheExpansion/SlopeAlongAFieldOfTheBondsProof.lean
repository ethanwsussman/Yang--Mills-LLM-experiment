import YangMills.Construction.ResponseInTheExpansion.SlopeAlongAFieldOfTheBonds
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.LinearResponse
namespace BondFieldSlope
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem partialAlongBondField_bounds {ρ : ℝ} {A : BondField ι → ℝ} {b : ι} {z : BondVector → BondVector}
    {B₁ Mz Mz' : ℝ} {B₂ : ι → ℝ}
    (hA : ∀ ζ : BondField ι, (∀ b, ‖ζ b‖ < ρ) → ContDiffAt ℝ 3 A ζ)
    (hz : ∀ v : BondVector, ‖v‖ < ρ → ContDiffAt ℝ 1 z v)
    (hzM : ∀ v : BondVector, ‖v‖ < ρ → ‖z v‖ ≤ Mz) (hzD : ∀ v : BondVector, ‖v‖ < ρ → ‖fderiv ℝ z v‖ ≤ Mz')
    (hB₁0 : 0 ≤ B₁) (hB₂0 : ∀ b', 0 ≤ B₂ b') (hMz0 : 0 ≤ Mz) (hMz'0 : 0 ≤ Mz')
    (hB₁ : ∀ ζ : BondField ι, (∀ b, ‖ζ b‖ < ρ) → ∀ u : BondVector, |fderiv ℝ A ζ (Pi.single b u)| ≤ B₁ * ‖u‖)
    (hB₂ : ∀ ζ : BondField ι, (∀ b, ‖ζ b‖ < ρ) → ∀ (b' : ι) (u u' : BondVector),
      |fderiv ℝ (fderiv ℝ A) ζ (Pi.single b' u) (Pi.single b u')| ≤ B₂ b' * ‖u‖ * ‖u'‖) :
    ContDiffOn ℝ 1 (fun η : BondField ι => bondPartialDeriv A b η (z (η b))) {η | ∀ b, ‖η b‖ < ρ} ∧
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |bondPartialDeriv A b η (z (η b))| ≤ B₁ * Mz) ∧
    ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b' : ι,
      bondGradNorm (fun η : BondField ι => bondPartialDeriv A b η (z (η b))) b' η ≤
        B₂ b' * Mz + (if b' = b then B₁ * Mz' else 0) := by
  set Lb : BondVector →L[ℝ] BondField ι := ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b with hLb
  set Pb : BondField ι →L[ℝ] BondVector :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b with hPb
  set zh : BondField ι → BondField ι := fun η => Lb (z (Pb η)) with hzh
  have hH : (fun η : BondField ι => bondPartialDeriv A b η (z (η b))) = fun η => fderiv ℝ A η (zh η) := rfl
  have hΦ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ 1 (fderiv ℝ A) η := fun η hη =>
    (hA η hη).fderiv_right (m := 1) (by norm_num)
  have hzc : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ 1 zh η := fun η hη => by
    have h1 : ContDiffAt ℝ 1 (fun η : BondField ι => z (Pb η)) η :=
      ContDiffAt.comp η (hz (Pb η) (hη b)) Pb.contDiff.contDiffAt
    exact Lb.contDiff.contDiffAt.comp η h1
  refine ⟨?_, fun η hη => ?_, fun η hη b' => ?_⟩
  · rw [hH]
    exact fun η hη => ((hΦ η hη).clm_apply (hzc η hη)).contDiffWithinAt
  · have h1 := hB₁ η hη (z (η b))
    refine h1.trans (mul_le_mul_of_nonneg_left (hzM _ (hη b)) hB₁0)
  · have hΦd : HasFDerivAt (fderiv ℝ A) (fderiv ℝ (fderiv ℝ A) η) η :=
      ((hΦ η hη).differentiableAt (by simp)).hasFDerivAt
    have hzd : HasFDerivAt (fun v => z v) (fderiv ℝ z (Pb η)) (Pb η) :=
      ((hz (Pb η) (hη b)).differentiableAt (by simp)).hasFDerivAt
    have hzhd : HasFDerivAt zh (Lb.comp ((fderiv ℝ z (Pb η)).comp Pb)) η :=
      Lb.hasFDerivAt.comp η (hzd.comp η Pb.hasFDerivAt)
    have hd := hΦd.clm_apply hzhd
    have hfd : fderiv ℝ (fun η : BondField ι => bondPartialDeriv A b η (z (η b))) η =
        (fderiv ℝ A η).comp (Lb.comp ((fderiv ℝ z (Pb η)).comp Pb)) +
          (fderiv ℝ (fderiv ℝ A) η).flip (zh η) := by
      rw [hH]
      exact hd.fderiv
    unfold bondGradNorm
    rw [hfd]
    have hnn : 0 ≤ B₂ b' * Mz + (if b' = b then B₁ * Mz' else 0) := by
      have := hB₂0 b'
      split_ifs <;> positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hnn fun u => ?_
    have e1 : ((fderiv ℝ A η).comp (Lb.comp ((fderiv ℝ z (Pb η)).comp Pb)) +
        (fderiv ℝ (fderiv ℝ A) η).flip (zh η)).comp
        (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b') u =
        fderiv ℝ A η (Pi.single b (fderiv ℝ z (η b) ((Pi.single b' u : BondField ι) b))) +
          fderiv ℝ (fderiv ℝ A) η (Pi.single b' u) (Pi.single b (z (η b))) := rfl
    rw [e1]
    have t1 : |fderiv ℝ (fderiv ℝ A) η (Pi.single b' u) (Pi.single b (z (η b)))| ≤ B₂ b' * Mz * ‖u‖ := by
      refine (hB₂ η hη b' u (z (η b))).trans ?_
      have h2 := hzM _ (hη b)
      have h3 := hB₂0 b'
      calc B₂ b' * ‖u‖ * ‖z (η b)‖ ≤ B₂ b' * ‖u‖ * Mz := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    have t2 : |fderiv ℝ A η (Pi.single b (fderiv ℝ z (η b) ((Pi.single b' u : BondField ι) b)))| ≤
        (if b' = b then B₁ * Mz' else 0) * ‖u‖ := by
      by_cases hb : b' = b
      · subst hb
        rw [if_pos rfl, Pi.single_eq_same]
        refine (hB₁ η hη _).trans ?_
        have h2 := (fderiv ℝ z (η b')).le_opNorm u
        have h3 := hzD _ (hη b')
        calc B₁ * ‖fderiv ℝ z (η b') u‖ ≤ B₁ * (Mz' * ‖u‖) :=
              mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))) hB₁0
          _ = _ := by ring
      · rw [if_neg hb, Pi.single_eq_of_ne (Ne.symm hb)]
        simp
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    have e2 : (B₂ b' * Mz + (if b' = b then B₁ * Mz' else 0)) * ‖u‖ =
        (if b' = b then B₁ * Mz' else 0) * ‖u‖ + B₂ b' * Mz * ‖u‖ := by ring
    rw [e2]
    exact add_le_add t2 t1
end BondFieldSlope
open BondFieldSlope in
theorem partialAlongBondFieldRegular_holds : PartialAlongBondFieldRegular :=
  fun hA hz hzM hzD hB₁0 hB₂0 hMz0 hMz'0 hB₁ hB₂ =>
    partialAlongBondField_bounds hA hz hzM hzD hB₁0 hB₂0 hMz0 hMz'0 hB₁ hB₂
end YangMills.Construction.LinearResponse
end
