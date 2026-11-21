import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def sincAngle (a : ℝ) : ℝ := if a = 0 then 1 else a⁻¹ * Real.sin a
def UnitaryLogConjugationProperties : Prop :=
  (∀ A ∈ hermitianTraceless,
    A ^ 2 = ((operatorNorm A : ℂ) ^ 2) • (1 : ComplexMatrix2) ∧
    matExp (Complex.I • A) =
      (Real.cos (operatorNorm A) : ℂ) • (1 : ComplexMatrix2) +
        (Complex.I * (sincAngle (operatorNorm A) : ℂ)) • A ∧
    matExp (Complex.I • A) ∈ specialUnitary) ∧
  (∀ W ∈ unitaryLogDomain,
    ∃! Y : ComplexMatrix2,
      Y ∈ hermitianTraceless ∧ operatorNorm Y < Real.pi ∧ matExp (Complex.I • Y) = W) ∧
  (∀ W ∈ unitaryLogDomain, ∀ T ∈ specialUnitary,
    T * W * T⁻¹ ∈ unitaryLogDomain ∧
      unitaryLog (T * W * T⁻¹) = T * unitaryLog W * T⁻¹)
end YangMills.Construction.Matrices.ComplexMatrix2
