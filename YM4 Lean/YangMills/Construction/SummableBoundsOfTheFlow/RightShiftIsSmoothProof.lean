import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftExists
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
namespace RightTranslationSmooth
instance instFiniteDimensionalImaginaryQuaternions : FiniteDimensional ℝ imaginaryQuaternions :=
  FiniteDimensional.finiteDimensional_submodule _
instance instCompleteSpaceImaginaryQuaternions : CompleteSpace imaginaryQuaternions :=
  FiniteDimensional.complete ℝ imaginaryQuaternions
def imaginaryPart : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun q := ⟨(⟨0, q.imI, q.imJ, q.imK⟩ : ℍ[ℝ]), rfl⟩
  map_add' a b := Subtype.ext (by ext <;> first | rfl | (show (0 : ℝ) = 0 + 0; simp))
  map_smul' r a := Subtype.ext (by ext <;> first | rfl | (show (0 : ℝ) = r * 0; simp))
def imaginaryPartCLM : ℍ[ℝ] →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap imaginaryPart
theorem imaginaryPartCLM_coe (X : imaginaryQuaternions) : imaginaryPartCLM (X : ℍ[ℝ]) = X := by
  refine Subtype.ext ?_
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  change (⟨0, (X : ℍ[ℝ]).imI, (X : ℍ[ℝ]).imJ, (X : ℍ[ℝ]).imK⟩ : ℍ[ℝ]) = (X : ℍ[ℝ])
  ext <;> simp [hre]
theorem contDiff_exp_quaternion :
    ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
def expDerivPullback (w : imaginaryQuaternions) : imaginaryQuaternions →L[ℝ] imaginaryQuaternions :=
  imaginaryPartCLM.comp ((ContinuousLinearMap.mul ℝ ℍ[ℝ] (NormedSpace.exp (-(w : ℍ[ℝ])))).comp
    ((fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ])).comp imaginaryQuaternions.subtypeL))
theorem contDiff_expDerivPullback : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) expDerivPullback := by
  have hincl : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) :=
    imaginaryQuaternions.subtypeL.contDiff
  have hderiv : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞)
      (fun w : imaginaryQuaternions => fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ])) :=
    (contDiff_exp_quaternion.fderiv_right (m := 3) (by norm_num)).comp hincl
  have hexp : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞)
      (fun w : imaginaryQuaternions => NormedSpace.exp (-(w : ℍ[ℝ]))) :=
    (contDiff_exp_quaternion.of_le (by norm_num)).comp hincl.neg
  have hmul : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞)
      (fun w : imaginaryQuaternions => ContinuousLinearMap.mul ℝ ℍ[ℝ] (NormedSpace.exp (-(w : ℍ[ℝ])))) :=
    (ContinuousLinearMap.mul ℝ ℍ[ℝ]).contDiff.comp hexp
  exact contDiff_const.clm_comp (hmul.clm_comp (hderiv.clm_comp contDiff_const))
theorem expDerivPullback_of_isRightTranslationDeriv (w X u : imaginaryQuaternions)
    (h : IsRightTranslationDeriv w X u) : expDerivPullback w u = X := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  have hd : DifferentiableAt ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) ((w : ℍ[ℝ]) + (0 : ℝ) • (u : ℍ[ℝ])) :=
    contDiff_exp_quaternion.differentiable (by simp) _
  have hline : HasDerivAt (fun τ : ℝ => (w : ℍ[ℝ]) + τ • (u : ℍ[ℝ])) (u : ℍ[ℝ]) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (u : ℍ[ℝ])).const_add (w : ℍ[ℝ])
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  have heq := hcomp.unique h
  simp only [zero_smul, add_zero] at heq
  have hprod : NormedSpace.exp (-(w : ℍ[ℝ])) *
      fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ]) (u : ℍ[ℝ]) = (X : ℍ[ℝ]) := by
    rw [heq, ← mul_assoc, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel,
      NormedSpace.exp_zero, one_mul]
  change imaginaryPartCLM (NormedSpace.exp (-(w : ℍ[ℝ])) *
    fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ]) (u : ℍ[ℝ])) = X
  rw [hprod, imaginaryPartCLM_coe]
end RightTranslationSmooth
open RightTranslationSmooth in
theorem rightTranslationSmooth_of_exists (hE : rightTranslationDerivExistsStatement) :
    rightTranslationSmooth := by
  obtain ⟨Th₀, hTh₀⟩ := hE
  have hequiv : ∀ w : imaginaryQuaternions, ‖w‖ < Real.pi →
      ∃ e : imaginaryQuaternions ≃L[ℝ] imaginaryQuaternions,
        (e : imaginaryQuaternions →L[ℝ] imaginaryQuaternions) = expDerivPullback w := by
    intro w hw
    have hsurj : Function.Surjective
        (expDerivPullback w : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions) := fun Y =>
      ⟨Th₀ w Y, expDerivPullback_of_isRightTranslationDeriv w Y _ (hTh₀ w Y hw)⟩
    have hinj := LinearMap.injective_iff_surjective.2 hsurj
    let e := (LinearEquiv.ofBijective
      (expDerivPullback w : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions)
      ⟨hinj, hsurj⟩).toContinuousLinearEquiv
    exact ⟨e, ContinuousLinearMap.ext fun X => rfl⟩
  set Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions :=
    fun w => ContinuousLinearMap.inverse (expDerivPullback w) with hThd
  have huniq : ∀ w X u : imaginaryQuaternions, ‖w‖ < Real.pi →
      IsRightTranslationDeriv w X u → u = Th w X := by
    intro w X u hw hs
    obtain ⟨e, he⟩ := hequiv w hw
    have hpull := expDerivPullback_of_isRightTranslationDeriv w X u hs
    simp only [hThd]
    rw [← he, ContinuousLinearMap.inverse_equiv, ← hpull, ← he]
    simp
  have hsmooth : ∀ w : imaginaryQuaternions, ‖w‖ < Real.pi →
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Th w := by
    intro w hw
    obtain ⟨e, he⟩ := hequiv w hw
    have hinv : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞)
        (ContinuousLinearMap.inverse :
          (imaginaryQuaternions →L[ℝ] imaginaryQuaternions) →
            imaginaryQuaternions →L[ℝ] imaginaryQuaternions)
        (expDerivPullback w) := by
      rw [← he]
      exact contDiffAt_map_inverse e
    exact ContDiffAt.comp w hinv contDiff_expDerivPullback.contDiffAt
  have : ProperSpace imaginaryQuaternions := FiniteDimensional.proper_real imaginaryQuaternions
  have hπ : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ‖w‖ < Real.pi :=
    fun w hw => lt_of_le_of_lt hw (by linarith [Real.pi_gt_three])
  have hcont : ∀ j : ℕ, j ≤ 3 → ∃ C : ℝ,
      ∀ w ∈ Metric.closedBall (0 : imaginaryQuaternions) 1, ‖iteratedFDeriv ℝ j Th w‖ ≤ C := by
    intro j hj
    refine (isCompact_closedBall (0 : imaginaryQuaternions) 1).exists_bound_of_continuousOn
      fun w hw => ?_
    have hw1 : ‖w‖ ≤ 1 := by simpa using hw
    exact ((hsmooth w (hπ w hw1)).continuousAt_iteratedFDeriv (by exact_mod_cast hj)).continuousWithinAt
  obtain ⟨C0, h0⟩ := hcont 0 (by omega)
  obtain ⟨C1, h1⟩ := hcont 1 (by omega)
  obtain ⟨C2, h2⟩ := hcont 2 (by omega)
  obtain ⟨C3, h3⟩ := hcont 3 le_rfl
  refine ⟨Th, |C0| + |C1| + |C2| + |C3|, by positivity, huniq, fun w X hw => ?_, hsmooth,
    fun w j hw hj => ?_⟩
  · have hsame := huniq w X _ hw (hTh₀ w X hw)
    rw [← hsame]
    exact hTh₀ w X hw
  · have hmem : w ∈ Metric.closedBall (0 : imaginaryQuaternions) 1 := by simpa using hw
    have a0 := abs_nonneg C0
    have a1 := abs_nonneg C1
    have a2 := abs_nonneg C2
    have a3 := abs_nonneg C3
    interval_cases j
    · exact (h0 w hmem).trans (by linarith [le_abs_self C0])
    · exact (h1 w hmem).trans (by linarith [le_abs_self C1])
    · exact (h2 w hmem).trans (by linarith [le_abs_self C2])
    · exact (h3 w hmem).trans (by linarith [le_abs_self C3])
end Interpolation
end YangMills.Construction
end
