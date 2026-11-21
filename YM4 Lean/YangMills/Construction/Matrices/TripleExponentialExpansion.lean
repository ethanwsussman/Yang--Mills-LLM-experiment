import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Matrices.TripleExponentialRadius
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def iHermitianTraceless : Set ComplexMatrix2 := {A | ∃ B ∈ hermitianTraceless, A = Complex.I • B}
def TripleExpExpansionStatement : Prop :=
  (∀ A B C : ComplexMatrix2, operatorNorm A ≤ tripleExpRadius → operatorNorm B ≤ tripleExpRadius →
    operatorNorm C ≤ tripleExpRadius →
    operatorNorm (matExp A * matExp B * matExp C - 1) ≤ 1 / 2 ∧
    operatorNorm (logSeries (matExp A * matExp B * matExp C) - (A + B + C) -
        (1 / 2 : ℂ) • (⁅A, B⁆ + ⁅A, C⁆ + ⁅B, C⁆)) ≤
      9 * (operatorNorm A + operatorNorm B + operatorNorm C) ^ 3 ∧
    (A ∈ iHermitianTraceless → B ∈ iHermitianTraceless → C ∈ iHermitianTraceless →
      Complex.I⁻¹ • logSeries (matExp A * matExp B * matExp C) ∈ hermitianTraceless ∧
      operatorNorm (Complex.I⁻¹ • logSeries (matExp A * matExp B * matExp C)) < Real.pi / 3)) ∧
  Coordinates.ComplexCoordinates.IsHolomorphicVia (E := Fin 3 → ComplexMatrix2)
    (Coordinates.ComplexCoordinates.productEquiv
      fun _ : Fin 3 => Coordinates.ComplexCoordinates.Component.matrix)
    Coordinates.ComplexCoordinates.matrixEquiv {W | ∀ i, operatorNorm (W i) < tripleExpRadius}
    fun W => logSeries (matExp (W 0) * matExp (W 1) * matExp (W 2))
end YangMills.Construction.Matrices.ComplexMatrix2
end
