import YangMills.Construction.RunningCouplingSlope.DeterminantOfTheLeftFrame
import YangMills.Construction.SoftAverages.HaarCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace RunningCouplingSlope
open SoftAverages SoftAverages.FiniteLinkFunctions SoftAverages.HaarCoordinates
private def imaginaryParts (w : imaginaryQuaternions) : Coordinates :=
  ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK]
private theorem pureQuaternionCLM_imaginaryParts (w : imaginaryQuaternions) :
    pureQuaternionCLM (imaginaryParts w) = (w : ℍ[ℝ]) := by
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact hre.symm
  · rfl
  · rfl
  · rfl
private theorem pureQuaternionCLM_basisVec (a : Fin 3) :
    pureQuaternionCLM (basisVec a) = ((imaginaryBasis a : imaginaryQuaternions) : ℍ[ℝ]) := by
  have hre : ∀ v : Coordinates, (pureQuaternionCLM v).re = 0 := fun _ => rfl
  have hI : ∀ v : Coordinates, (pureQuaternionCLM v).imI = v 0 := fun _ => rfl
  have hJ : ∀ v : Coordinates, (pureQuaternionCLM v).imJ = v 1 := fun _ => rfl
  have hK : ∀ v : Coordinates, (pureQuaternionCLM v).imK = v 2 := fun _ => rfl
  fin_cases a <;> refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp [hre, hI, hJ, hK, imaginaryBasis, toImaginary, basisVec]
private theorem imaginaryCoord_eq_imCoord (a : Fin 3) (q : ℍ[ℝ]) :
    imaginaryCoord a q = imCoord a q := by
  refine (Quaternion.inner_def _ _).trans ?_
  rw [Quaternion.re_mul]
  simp only [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  fin_cases a <;> simp [imaginaryBasis, toImaginary, imCoord]
private theorem expDeriv_imaginaryParts (w : imaginaryQuaternions) (v : Coordinates) :
    expDeriv (imaginaryParts w) v =
      fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ]) (pureQuaternionCLM v) := by
  have hexp : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])
      (fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ]))
      (pureQuaternionCLM (imaginaryParts w)) := by
    rw [pureQuaternionCLM_imaginaryParts]
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) _).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt expImag
      ((fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ])).comp pureQuaternionCLM)
      (imaginaryParts w) :=
    hexp.comp (imaginaryParts w) pureQuaternionCLM.hasFDerivAt
  have heq := (hasFDerivAt_expImag (imaginaryParts w)).unique hcomp
  rw [heq]
  rfl
private theorem star_expImag_imaginaryParts (w : imaginaryQuaternions) :
    star (expImag (imaginaryParts w)) = NormedSpace.exp (-(w : ℍ[ℝ])) := by
  have hstar : star (w : ℍ[ℝ]) = -(w : ℍ[ℝ]) := by
    have hre : (w : ℍ[ℝ]).re = 0 := w.2
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [hre]
  rw [expImag_eq_exp, pureQuaternionCLM_imaginaryParts, ← hstar]
  exact NormedSpace.star_exp _
private theorem leftExpDifferential_eq_frameMat (w : imaginaryQuaternions) :
    leftExpDifferential w = frameMat (imaginaryParts w) := by
  ext a b
  simp only [leftExpDifferential, frameMat, Matrix.of_apply, rightFrame]
  rw [expDeriv_imaginaryParts, star_expImag_imaginaryParts, imaginaryCoord_eq_imCoord,
    pureQuaternionCLM_basisVec]
theorem leftExpDifferentialDet_holds : LeftExpDifferentialDet := by
  intro w
  have hnorm : ‖w‖ = Real.sqrt (∑ i, imaginaryParts w i ^ 2) := by
    have h := norm_pureQuaternionCLM (imaginaryParts w)
    rw [pureQuaternionCLM_imaginaryParts] at h
    exact h
  rw [leftExpDifferential_eq_frameMat, det_frameMat]
  unfold SoftAverages.haarDensity
  split_ifs with hzero
  · rw [hnorm, hzero]
    simp
  · have hne : ‖w‖ ≠ 0 := by
      intro h
      apply hzero
      have hw : w = 0 := norm_eq_zero.mp h
      subst hw
      funext i
      fin_cases i <;> simp [imaginaryParts]
    rw [← hnorm, Real.sinc_of_ne_zero hne]
end RunningCouplingSlope
end YangMills.Construction
end
