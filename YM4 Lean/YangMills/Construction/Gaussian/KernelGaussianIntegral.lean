import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Gaussian.KernelIntegral
def formMatrixInBasis {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : E →ₗ[ℝ] F)
    (Q : QuadraticForm ℝ (LinearMap.ker L)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (LinearMap.ker L)) : Matrix ι ι ℝ :=
  LinearMap.BilinForm.toMatrix b.toBasis (QuadraticMap.associated Q)
def GaussianIntegralOnKernel : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →ₗ[ℝ] F), Function.Surjective L →
    ∀ Q : QuadraticForm ℝ (LinearMap.ker L), Q.PosDef →
      0 < LinearMap.det (L ∘ₗ LinearMap.adjoint L) ∧
      ∃ d : ℝ, 0 < d ∧
        (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ (LinearMap.ker L)),
          (formMatrixInBasis L Q b).det = d) ∧
        (letI : MeasurableSpace (LinearMap.ker L) := borel _
         haveI : BorelSpace (LinearMap.ker L) := ⟨rfl⟩
         Integrable (fun x : LinearMap.ker L => Real.exp (-(1 / 2) * Q x)) ∧
         0 < ∫ x : LinearMap.ker L, Real.exp (-(1 / 2) * Q x) ∧
         ∫ x : LinearMap.ker L, Real.exp (-(1 / 2) * Q x) =
           (2 * Real.pi) ^ ((Module.finrank ℝ (LinearMap.ker L) : ℝ) / 2) * d ^ (-(1 / 2) : ℝ))
end YangMills.Construction.Gaussian.KernelIntegral
end
