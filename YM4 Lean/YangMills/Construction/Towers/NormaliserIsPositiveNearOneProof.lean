import YangMills.Construction.Gaussian.KernelGaussianIntegral
import YangMills.Construction.Towers.NormaliserIsPositiveNearOne
import YangMills.Construction.Towers.SpacesOfFormsAtAFiniteSide
import YangMills.Construction.Towers.TheFormOnAFibreOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.NormaliserPositivity
open GaussianConstraint in
theorem constrainedGaussianNumberOfCores_pos (hG : Gaussian.KernelIntegral.GaussianIntegralOnKernel)
    {E F : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (c₁ : InnerProductSpace.Core ℝ E) (c₂ : InnerProductSpace.Core ℝ F) (M : E →ₗ[ℝ] F)
    (Q : QuadraticForm ℝ (LinearMap.ker M)) (hM : Function.Surjective M) (hQ : Q.PosDef) :
    0 < constrainedGaussianNumberOfCores c₁ c₂ M Q := by
  letI := c₁.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c₁.toCore
  letI := c₂.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c₂.toCore
  obtain ⟨hdet, d, -, -, -, hint, -⟩ := hG E F M hM Q hQ
  simp only [constrainedGaussianNumberOfCores, constrainedGaussianNumber, kernelGaussianIntegral]
  exact mul_pos (Real.rpow_pos_of_pos hdet _) hint
theorem gaussianNormaliser_pos_near_identity (hF : CriticalFibreHessianPosDef)
    (hS : FiniteSideFormSpaces) (hG : Gaussian.KernelIntegral.GaussianIntegralOnKernel) :
    GaussianNormaliserPositiveNearOne := by
  intro L m k hL hm i hi
  obtain ⟨-, f₁, -, c₁, h₁⟩ := hS L m k i hL hm (by omega)
  obtain ⟨-, f₂, -, c₂, h₂⟩ := hS L m k (i + 1) hL hm hi
  have hE : EdgeFormsEuclidean L m k i ∧ EdgeFormsEuclidean L m k (i + 1) :=
    ⟨⟨f₁, c₁, fun B B' => by rw [h₁ B B', Complex.ofReal_re]⟩,
      ⟨f₂, c₂, fun B B' => by rw [h₂ B B', Complex.ofReal_re]⟩⟩
  have := hE.1.1
  have := hE.2.1
  refine Filter.Eventually.mono (hF L m k hL hm i hi) fun A hA => ?_
  obtain ⟨-, hM, -, -, hQ⟩ := hA
  have hN : gaussianNormaliser L m k i A =
      GaussianConstraint.constrainedGaussianNumberOfCores hE.1.2.choose hE.2.2.choose
        (constraintDifferential L m k i A) (fibreHessianForm L m k i A) := by
    unfold gaussianNormaliser constrainedGaussianOnEdgeForms
    rw [dif_pos hE]
  rw [hN]
  exact constrainedGaussianNumberOfCores_pos hG _ _ _ _ hM hQ
end YangMills.Construction.Tower.NormaliserPositivity
end
