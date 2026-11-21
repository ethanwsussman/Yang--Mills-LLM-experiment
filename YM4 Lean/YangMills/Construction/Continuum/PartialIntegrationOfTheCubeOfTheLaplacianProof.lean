import YangMills.Construction.TwoPoints.ParametrixOfTheCubedLaplacianProof
import YangMills.Construction.Continuum.PartialIntegrationOfTheCubeOfTheLaplacian
import Mathlib
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open TestFunctions EuclideanFunctionals
namespace Parametrix
namespace LaplacianCube
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem partialDerivR4_eq_fderiv {u : R4 → F} (hu : Differentiable ℝ u) (ν : Fin 4) (p : R4) :
    partialDerivR4 ν u p = fderiv ℝ u p (Pi.single ν (1 : ℝ)) :=
  (hu p).lineDeriv_eq_fderiv
theorem differentiable_of_smooth {u : R4 → F} (hu : ContDiff ℝ ∞ u) : Differentiable ℝ u :=
  hu.differentiable (by simp)
theorem partialDerivR4_eq_fun {u : R4 → F} (hu : ContDiff ℝ ∞ u) (ν : Fin 4) :
    partialDerivR4 ν u = fun p => fderiv ℝ u p (Pi.single ν (1 : ℝ)) :=
  funext (partialDerivR4_eq_fderiv (differentiable_of_smooth hu) ν)
theorem contDiff_partialDerivR4 {u : R4 → F} (hu : ContDiff ℝ ∞ u) (ν : Fin 4) :
    ContDiff ℝ ∞ (partialDerivR4 ν u) := by apply _root_.YangMills.Construction.TwoPoints.LaplacianCubeParametrix.contDiff_partialDerivR4 <;> assumption
theorem hasCompactSupport_partialDerivR4 {u : R4 → F} (hu : ContDiff ℝ ∞ u)
    (hcs : HasCompactSupport u) (ν : Fin 4) : HasCompactSupport (partialDerivR4 ν u) := by apply _root_.YangMills.Construction.TwoPoints.LaplacianCubeParametrix.hasCompactSupport_partialDerivR4 <;> assumption
theorem contDiff_laplacianR4 {u : R4 → F} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (laplacianR4 u) := by apply _root_.YangMills.Construction.TwoPoints.LaplacianCubeParametrix.contDiff_laplacianR4 <;> assumption
theorem hasCompactSupport_laplacianR4 {u : R4 → F} (hu : ContDiff ℝ ∞ u)
    (hcs : HasCompactSupport u) : HasCompactSupport (laplacianR4 u) := by apply _root_.YangMills.Construction.TwoPoints.LaplacianCubeParametrix.hasCompactSupport_laplacianR4 <;> assumption
theorem integral_partialDerivR4_mul {φ ψ : R4 → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hcs : HasCompactSupport φ) (hψ : ContDiff ℝ ∞ ψ) (ν : Fin 4) :
    ∫ p, partialDerivR4 ν φ p * ψ p = -∫ p, φ p * partialDerivR4 ν ψ p := by
  have hφ' := contDiff_partialDerivR4 hφ ν
  have hcs' := hasCompactSupport_partialDerivR4 hφ hcs ν
  have hψ' := contDiff_partialDerivR4 hψ ν
  have int1 : Integrable (fun p => partialDerivR4 ν φ p * ψ p) :=
    (hφ'.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcs'.mul_right
  have int2 : Integrable (fun p => φ p * partialDerivR4 ν ψ p) :=
    (hφ.continuous.mul hψ'.continuous).integrable_of_hasCompactSupport hcs.mul_right
  have int3 : Integrable (fun p => φ p * ψ p) :=
    (hφ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcs.mul_right
  have hdφ := differentiable_of_smooth hφ
  have hdψ := differentiable_of_smooth hψ
  rw [partialDerivR4_eq_fun hφ ν] at int1 ⊢
  rw [partialDerivR4_eq_fun hψ ν] at int2 ⊢
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable int1 int2 int3
    (fun p _ => hdφ p) (fun p _ => hdψ p), neg_neg]
theorem integral_laplacianR4_mul {φ ψ : R4 → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hcs : HasCompactSupport φ) (hψ : ContDiff ℝ ∞ ψ) :
    ∫ p, laplacianR4 φ p * ψ p = ∫ p, φ p * laplacianR4 ψ p := by
  have term : ∀ ν : Fin 4, ∫ p, partialDerivR4 ν (partialDerivR4 ν φ) p * ψ p =
      ∫ p, φ p * partialDerivR4 ν (partialDerivR4 ν ψ) p := fun ν => by
    rw [integral_partialDerivR4_mul (contDiff_partialDerivR4 hφ ν)
      (hasCompactSupport_partialDerivR4 hφ hcs ν) hψ ν,
      integral_partialDerivR4_mul hφ hcs (contDiff_partialDerivR4 hψ ν) ν, neg_neg]
  simp only [laplacianR4, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum, integral_finsetSum]
  · exact Finset.sum_congr rfl fun ν _ => term ν
  · intro ν _
    exact (hφ.continuous.mul (contDiff_partialDerivR4 (contDiff_partialDerivR4 hψ ν) ν).continuous
      ).integrable_of_hasCompactSupport hcs.mul_right
  · intro ν _
    have h1 := contDiff_partialDerivR4 (contDiff_partialDerivR4 hφ ν) ν
    have h2 := hasCompactSupport_partialDerivR4 (contDiff_partialDerivR4 hφ ν)
      (hasCompactSupport_partialDerivR4 hφ hcs ν) ν
    exact (h1.continuous.mul hψ.continuous).integrable_of_hasCompactSupport h2.mul_right
theorem partialDerivR4_ofReal {f : R4 → ℝ} (hf : Differentiable ℝ f) (ν : Fin 4) :
    partialDerivR4 ν (fun p => (f p : ℂ)) = fun p => ((partialDerivR4 ν f p : ℝ) : ℂ) := by
  funext p
  rw [partialDerivR4_eq_fderiv hf ν p]
  have h : HasDerivAt (fun t : ℝ => f (p + t • (Pi.single ν (1 : ℝ) : R4)))
      (fderiv ℝ f p (Pi.single ν (1 : ℝ))) 0 :=
    (hf p).hasFDerivAt.hasLineDerivAt (Pi.single ν (1 : ℝ))
  exact h.ofReal_comp.deriv
theorem laplacianR4_ofReal {f : R4 → ℝ} (hf : ContDiff ℝ ∞ f) :
    laplacianR4 (fun p => (f p : ℂ)) = fun p => ((laplacianR4 f p : ℝ) : ℂ) := by
  funext p
  simp only [laplacianR4, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [partialDerivR4_ofReal (differentiable_of_smooth hf) ν,
    partialDerivR4_ofReal (differentiable_of_smooth (contDiff_partialDerivR4 hf ν)) ν]
end LaplacianCube
open LaplacianCube in
theorem laplacianCubeSelfAdjoint_holds : LaplacianCubeSelfAdjoint := by
  intro φ f hφ hcs hf
  have hψ : ContDiff ℝ ∞ (fun p => (f p : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hf1 := contDiff_laplacianR4 hf
  have hf2 := contDiff_laplacianR4 hf1
  have hφ1 := contDiff_laplacianR4 hφ
  have hcs1 := hasCompactSupport_laplacianR4 hφ hcs
  have hφ2 := contDiff_laplacianR4 hφ1
  have hcs2 := hasCompactSupport_laplacianR4 hφ1 hcs1
  have lift : ∀ u : R4 → ℝ, ContDiff ℝ ∞ u → ContDiff ℝ ∞ (fun p => (u p : ℂ)) :=
    fun u hu => Complex.ofRealCLM.contDiff.comp hu
  calc ∫ p, laplacianR4^[3] φ p * (f p : ℂ)
      = ∫ p, laplacianR4 (laplacianR4 (laplacianR4 φ)) p * (f p : ℂ) := rfl
    _ = ∫ p, laplacianR4 (laplacianR4 φ) p * ((laplacianR4 f p : ℝ) : ℂ) := by
        rw [integral_laplacianR4_mul hφ2 hcs2 hψ, laplacianR4_ofReal hf]
    _ = ∫ p, laplacianR4 φ p * ((laplacianR4 (laplacianR4 f) p : ℝ) : ℂ) := by
        rw [integral_laplacianR4_mul hφ1 hcs1 (lift _ hf1), laplacianR4_ofReal hf1]
    _ = ∫ p, φ p * ((laplacianR4 (laplacianR4 (laplacianR4 f)) p : ℝ) : ℂ) := by
        rw [integral_laplacianR4_mul hφ hcs (lift _ hf2), laplacianR4_ofReal hf2]
    _ = ∫ p, φ p * Complex.ofReal (laplacianR4^[3] f p) := rfl
end Parametrix
end YangMills.Construction
end
