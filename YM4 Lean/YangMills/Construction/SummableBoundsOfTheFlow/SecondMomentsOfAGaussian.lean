import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.GaussianMoments
def quadForm {ι : Type} [Fintype ι] (A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ)
    (ζ : ι → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i, ∑ j, A i j * (ζ i.1 i.2 * ζ j.1 j.2)
def gaussianWeight {ι : Type} [Fintype ι] (A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ)
    (ζ : ι → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.exp (-(1 / 2 * quadForm A ζ))
def CovarianceEqInverse : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (m : ℝ), 0 < m → A.IsSymm →
    (∀ ζ : ι → EuclideanSpace ℝ (Fin 3), m * ∑ b, ‖ζ b‖ ^ 2 ≤ quadForm A ζ) →
    IsUnit A.det ∧ Integrable (gaussianWeight A) ∧ 0 < ∫ ζ, gaussianWeight A ζ ∧
      (∀ i j : ι × Fin 3, Integrable fun ζ : ι → EuclideanSpace ℝ (Fin 3) =>
        ζ i.1 i.2 * ζ j.1 j.2 * gaussianWeight A ζ) ∧
      ∀ i j : ι × Fin 3, (∫ ζ, ζ i.1 i.2 * ζ j.1 j.2 * gaussianWeight A ζ) / (∫ ζ, gaussianWeight A ζ) = A⁻¹ i j
end YangMills.Construction.GaussianMoments
end
