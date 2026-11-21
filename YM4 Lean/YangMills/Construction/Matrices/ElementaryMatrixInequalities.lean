import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def expListProduct {n : ℕ} (A : Fin n → ComplexMatrix2) : ComplexMatrix2 :=
  (List.ofFn fun j => matExp (A j)).prod
def BoundsBchRemainders (c : ℝ) : Prop :=
  ∀ A B : ComplexMatrix2, operatorNorm A ≤ 1 / 16 → operatorNorm B ≤ 1 / 16 →
    operatorNorm (bchRemainder A B) ≤ c * operatorNorm A * operatorNorm B ∧
    operatorNorm (logSeries (matExp (-B) * matExp (B + A)) - A) ≤ c * operatorNorm A * operatorNorm B ∧
    operatorNorm (logSeries (matExp (-B + A) * matExp B) - A) ≤ c * operatorNorm A * operatorNorm B
def ElementaryInequalitiesStatement : Prop :=
  (∀ (n : ℕ), n ≤ 4 → ∀ A : Fin n → ComplexMatrix2,
    (∑ j, operatorNorm (A j) ≤ 1 →
      operatorNorm (expListProduct A - 1 - ∑ j, A j) ≤ (∑ j, operatorNorm (A j)) ^ 2 ∧
      operatorNorm (expListProduct A - matExp (∑ j, A j)) ≤ 2 * (∑ j, operatorNorm (A j)) ^ 2) ∧
    (∑ j, operatorNorm (A j) ≤ 1 / 4 →
      operatorNorm (logSeries (expListProduct A) - ∑ j, A j) ≤ 4 * (∑ j, operatorNorm (A j)) ^ 2)) ∧
  (∀ (ρ M : ℝ) (f : ComplexMatrix2 × ComplexMatrix2 → ComplexMatrix2),
    Coordinates.ComplexCoordinates.IsHolomorphicVia Coordinates.ComplexCoordinates.matrixPairEquiv
      Coordinates.ComplexCoordinates.matrixEquiv
      {p | operatorNorm p.1 < ρ ∧ operatorNorm p.2 < ρ} f →
    (∀ A B : ComplexMatrix2, operatorNorm A < ρ → operatorNorm B < ρ → operatorNorm (f (A, B)) ≤ M) →
    (∀ B : ComplexMatrix2, operatorNorm B < ρ → f (0, B) = 0) →
    (∀ A : ComplexMatrix2, operatorNorm A < ρ → f (A, 0) = 0) →
    ∀ A B : ComplexMatrix2, operatorNorm A < ρ → operatorNorm B < ρ →
      operatorNorm (f (A, B)) ≤ M * (ρ ^ 2)⁻¹ * operatorNorm A * operatorNorm B) ∧
  (∃ c : ℝ, 1 ≤ c ∧ BoundsBchRemainders c) ∧
  (∀ u ∈ specialUnitary, ∀ U ∈ specialUnitary,
    operatorNorm (u * U * u⁻¹ - U) ≤ 2 * operatorNorm (u - 1) * operatorNorm (U - 1)) ∧
  (∀ u ∈ specialUnitary, ∀ A : ComplexMatrix2,
    operatorNorm (conjugateBy u A - A) ≤ 2 * operatorNorm (u - 1) * operatorNorm A) ∧
  (∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
      [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
      (r M : ℝ) (f : V → W),
    DifferentiableOn ℂ f (Metric.ball 0 r) →
    (∀ a ∈ Metric.ball (0 : V) r, ‖f a‖ ≤ M) →
    ∀ a ∈ Metric.ball (0 : V) r,
      (∀ v : V, ‖fderiv ℂ f a v‖ ≤ M * ‖v‖ / (r - ‖a‖)) ∧
      ‖f a - f 0 - fderiv ℂ f 0 a‖ ≤ M * ‖a‖ ^ 2 / (r * (r - ‖a‖)) ∧
      (f 0 = 0 → ‖f a‖ ≤ M * ‖a‖ / r)) ∧
  (∀ A ∈ hermitianTraceless, operatorNorm A ≤ Real.pi →
    operatorNorm A ≤ operatorNorm (matExp (Complex.I • A) - 1) + 1 / 24 * operatorNorm A ^ 3)
end YangMills.Construction.Matrices.ComplexMatrix2
