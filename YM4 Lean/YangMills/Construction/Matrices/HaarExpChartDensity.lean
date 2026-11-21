import YangMills.Construction.Matrices.UnitaryLogConjugation
import Mathlib
open MeasureTheory
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def haarExpDensity (Y : ComplexMatrix2) : ℝ :=
  (2 * Real.pi ^ 2)⁻¹ * sincAngle (operatorNorm Y) ^ 2
open Classical in
def expChart (Y : LieElement) : specialUnitary :=
  if h : matExp (Complex.I • Y.toMatrix) ∈ specialUnitary then ⟨_, h⟩ else 1
def lieBallPi : Set LieElement := {Y | operatorNorm Y.toMatrix < Real.pi}
def HaarExpChartProperties : Prop :=
  ((∀ f : specialUnitary → ℂ, Measurable f → (∃ C : ℝ, ∀ U, ‖f U‖ ≤ C) →
      ∫ U, f U ∂haarProb =
        ∫ Y in lieBallPi, f (expChart Y) * (haarExpDensity Y.toMatrix : ℂ) ∂lieLebesgue) ∧
    haarProb {U : specialUnitary | (U : ComplexMatrix2) = -1} = 0 ∧
    haarProb = Measure.map expChart
      ((lieLebesgue.restrict lieBallPi).withDensity
        fun Y => ENNReal.ofReal (haarExpDensity Y.toMatrix)) ∧
    haarExpDensity 0 = (2 * Real.pi ^ 2)⁻¹) ∧
  (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : LieElement => haarExpDensity Y.toMatrix) ∧
    (∀ Y ∈ lieBallPi, 0 < haarExpDensity Y.toMatrix) ∧
    (∀ Y ∈ hermitianTraceless, ∀ T ∈ specialUnitary,
      conjugateBy T Y ∈ hermitianTraceless ∧ haarExpDensity (conjugateBy T Y) = haarExpDensity Y ∧
        haarExpDensity Y = haarExpDensity (-Y))) ∧
  ((∀ T T' : specialUnitary, Measure.map (fun U : specialUnitary => T * U * T') haarProb = haarProb) ∧
    Measure.map (fun U : specialUnitary => U⁻¹) haarProb = haarProb)
end YangMills.Construction.Matrices.ComplexMatrix2
