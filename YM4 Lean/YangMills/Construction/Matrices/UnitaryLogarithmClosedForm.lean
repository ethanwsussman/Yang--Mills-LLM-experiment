import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def unitaryLieLogClosedForm (U : ComplexMatrix2) : ComplexMatrix2 :=
  (1 / (Real.sinc (Real.arccos (halfTrace U).re) : ℂ)) •
    (1 / (2 * Complex.I)) • (U - U⁻¹)
def UnitaryLogarithmProperties : Prop :=
  (∀ Y ∈ hermitianTraceless,
    Y ^ 2 = ((operatorNorm Y : ℂ) ^ 2) • (1 : ComplexMatrix2) ∧
    matExp (Complex.I • Y) =
      (Real.cos (operatorNorm Y) : ℂ) • (1 : ComplexMatrix2) +
        (Complex.I * (Real.sinc (operatorNorm Y) : ℂ)) • Y ∧
    matExp (-(Complex.I • Y)) =
      (Real.cos (operatorNorm Y) : ℂ) • (1 : ComplexMatrix2) -
        (Complex.I * (Real.sinc (operatorNorm Y) : ℂ)) • Y ∧
    matExp (Complex.I • Y) ∈ specialUnitary) ∧
  (∀ U ∈ specialUnitary,
    (∃ t ∈ Set.Icc (-1 : ℝ) 1, halfTrace U = t) ∧ (halfTrace U = -1 → U = -1)) ∧
  (∀ U ∈ unitaryLogDomain, ∀ Y : ComplexMatrix2,
    (Y ∈ hermitianTraceless ∧ operatorNorm Y < Real.pi ∧ matExp (Complex.I • Y) = U) ↔
      Y = unitaryLieLogClosedForm U) ∧
  ContinuousOn unitaryLieLogClosedForm unitaryLogDomain ∧
  (∀ U ∈ unitaryLogDomain,
    unitaryLieLog U ∈ hermitianTraceless ∧ operatorNorm (unitaryLieLog U) < Real.pi ∧
      matExp (Complex.I • unitaryLieLog U) = U ∧
      ∃ Y ∈ hermitianTraceless, unitaryLog U = Complex.I • Y) ∧
  ContinuousOn unitaryLog unitaryLogDomain
end YangMills.Construction.Matrices.ComplexMatrix2
