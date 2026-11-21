import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def IsRotationAngle (W : ComplexMatrix2) (θ : ℝ) : Prop :=
  θ ∈ Set.Icc 0 Real.pi ∧
    W.charpoly.roots = {Complex.exp (θ * Complex.I), Complex.exp (-(θ * Complex.I))}
def rotationAngle (W : ComplexMatrix2) : ℝ := Classical.epsilon (IsRotationAngle W)
def SpecialUnitaryAngleBounds : Prop :=
  (∀ U ∈ specialUnitary,
    (∀ θ : ℝ, IsRotationAngle U θ ↔ θ = rotationAngle U) ∧
    (∀ θ ∈ Set.Icc 0 Real.pi, IsRotationAngle U θ ↔ (Real.cos θ : ℂ) = halfTrace U)) ∧
  (∀ U ∈ specialUnitary,
    operatorNorm (U - 1) = 2 * Real.sin (rotationAngle U / 2) ∧
    operatorNorm (U + 1) = 2 * Real.cos (rotationAngle U / 2) ∧
    rotationAngle U⁻¹ = rotationAngle U ∧
    (∀ g ∈ specialUnitary, rotationAngle U = rotationAngle (g * U * g⁻¹)) ∧
    2 / Real.pi * rotationAngle U ≤ operatorNorm (U - 1) ∧
    operatorNorm (U - 1) ≤ rotationAngle U) ∧
  (∀ A ∈ hermitianTraceless,
    A ^ 2 = ((operatorNorm A : ℂ) ^ 2) • (1 : ComplexMatrix2) ∧
    matExp (Complex.I • A) =
      (Real.cos (operatorNorm A) : ℂ) • (1 : ComplexMatrix2) +
        (Complex.I * (Real.sinc (operatorNorm A) : ℂ)) • A ∧
    rotationAngle (matExp (Complex.I • A)) ≤ operatorNorm A ∧
    (operatorNorm A ≤ Real.pi → rotationAngle (matExp (Complex.I • A)) = operatorNorm A)) ∧
  (∀ U ∈ unitaryLogDomain,
    operatorNorm (unitaryLieLog U) = rotationAngle U ∧
    (operatorNorm (U - 1) < 1 ↔ rotationAngle U < Real.pi / 3) ∧
    (rotationAngle U < Real.pi / 3 → unitaryLog U = logSeries U)) ∧
  (∀ U₁ ∈ specialUnitary, ∀ U₂ ∈ specialUnitary,
    rotationAngle (U₁ * U₂) ≤ rotationAngle U₁ + rotationAngle U₂) ∧
  (∀ (n : ℕ) (U V : Fin n → ComplexMatrix2), (∀ i, U i ∈ specialUnitary) →
    (∀ i, V i ∈ specialUnitary) →
    rotationAngle ((List.ofFn U).prod * ((List.ofFn V).prod)⁻¹) ≤
        ∑ i, rotationAngle (U i * (V i)⁻¹) ∧
    operatorNorm ((List.ofFn U).prod - (List.ofFn V).prod) ≤
        ∑ i, operatorNorm (U i * (V i)⁻¹ - 1)) ∧
  (∀ A ∈ hermitianTraceless, ∀ B ∈ hermitianTraceless,
    operatorNorm (matExp (Complex.I • A) - matExp (Complex.I • B)) ≤ operatorNorm (A - B)) ∧
  (∀ m : ℝ, 0 < m → m < Real.pi →
    (∀ Y ∈ hermitianTraceless, ∀ Y' ∈ hermitianTraceless, operatorNorm Y ≤ m →
      operatorNorm Y' ≤ m →
      operatorNorm (Y - Y') ≤
        m / Real.sin m * operatorNorm (matExp (Complex.I • Y) - matExp (Complex.I • Y'))) ∧
    (∀ U ∈ specialUnitary, ∀ U' ∈ specialUnitary, rotationAngle U ≤ m → rotationAngle U' ≤ m →
      operatorNorm (unitaryLieLog U - unitaryLieLog U') ≤
        m / Real.sin m * operatorNorm (U - U'))) ∧
  (∀ m : ℝ, 0 < m → m < Real.pi / 3 →
    m / Real.sin m < 2 * Real.pi / (3 * Real.sqrt 3)) ∧
  (∀ m : ℝ, 0 < m → m ≤ 1 → m / Real.sin m ≤ 1 + m ^ 2 / 5)
end YangMills.Construction.Matrices.ComplexMatrix2
