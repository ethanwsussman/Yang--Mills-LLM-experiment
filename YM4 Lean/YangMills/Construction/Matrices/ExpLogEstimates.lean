import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
def ExpLogEstimates : Prop :=
  (∀ Z : ComplexMatrix2,
    operatorNorm (matExp Z) ≤ Real.exp (operatorNorm Z) ∧
      operatorNorm (matExp Z - 1) ≤ Real.exp (operatorNorm Z) - 1) ∧
  (∀ (X X' : ComplexMatrix2) (r : ℝ), max (operatorNorm X) (operatorNorm X') ≤ r →
    operatorNorm (matExp X - matExp X') ≤ Real.exp r * operatorNorm (X - X') ∧
    operatorNorm (matExp X - matExp X' - (X - X')) ≤ (Real.exp r - 1) * operatorNorm (X - X')) ∧
  (∀ U X : ComplexMatrix2,
    operatorNorm (U * matExp X - 1) ≤ (1 + operatorNorm (U - 1)) * Real.exp (operatorNorm X) - 1) ∧
  (∀ E : ComplexMatrix2, operatorNorm E < 1 →
    operatorNorm (logSeries (1 + E)) ≤ -Real.log (1 - operatorNorm E) ∧
    -Real.log (1 - operatorNorm E) ≤ operatorNorm E / (1 - operatorNorm E) ∧
    IsUnit (1 + E) ∧
    operatorNorm ((1 + E)⁻¹ - 1) ≤ operatorNorm E / (1 - operatorNorm E) ∧
    matExp (logSeries (1 + E)) = 1 + E) ∧
  (∀ X : ComplexMatrix2, operatorNorm X < Real.log 2 →
    operatorNorm (matExp X - 1) < 1 ∧ logSeries (matExp X) = X) ∧
  (∀ X : ComplexMatrix2, (matExp X).det = Complex.exp (fullTrace X)) ∧
  (∀ M : ComplexMatrix2, M.det = 1 → operatorNorm (M - 1) ≤ 9 / 10 →
    fullTrace (logSeries M) = 0 ∧ logSeries M ∈ traceless) ∧
  (∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, operatorNorm (U - 1) < 1 →
    ∃ H : ComplexMatrix2, H.IsHermitian ∧ logSeries U = Complex.I • H ∧
      operatorNorm H < Real.pi / 3 ∧
      matExp (Complex.I • H) = U ∧ operatorNorm (U - 1) = 2 * Real.sin (operatorNorm H / 2) ∧
      (U.det = 1 →
        fullTrace H = 0 ∧ H ∈ hermitianTraceless ∧
          (∃ Y ∈ hermitianTraceless, logSeries U = Complex.I • Y) ∧ H = unitaryLieLog U)) ∧
  (∀ (ε : ℝ) (U V : ComplexMatrix2), 0 ≤ ε → ε < 1 → operatorNorm (U - 1) ≤ ε →
    operatorNorm (V - 1) ≤ ε →
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsUnit (1 + (t : ℂ) • (U - 1)) ∧ IsUnit (1 + (t : ℂ) • (V - 1))) ∧
    logSeries U - logSeries V =
      ∫ t in (0 : ℝ)..1, (1 + (t : ℂ) • (U - 1))⁻¹ * (U - V) * (1 + (t : ℂ) • (V - 1))⁻¹ ∧
    operatorNorm (logSeries U - logSeries V - (U - V)) ≤ ε / (1 - ε) * operatorNorm (U - V) ∧
    operatorNorm (logSeries U - logSeries V) ≤ 1 / (1 - ε) * operatorNorm (U - V)) ∧
  (∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
    operatorNorm (U - 1) < 1 → operatorNorm (V - 1) < 1 →
    operatorNorm (logSeries U - logSeries V) ≤ 2 * operatorNorm (U - V))
end YangMills.Construction.Matrices.ComplexMatrix2
