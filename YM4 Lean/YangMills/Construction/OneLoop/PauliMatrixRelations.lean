import YangMills.Construction.Matrices.ConjugationDeterminant
import YangMills.Construction.Matrices.SpecialUnitaryScalarVectorParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace OneLoop
open Matrices
def leviCivitaSymbol (i j k : Fin 3) : ℂ :=
  if hijk : Function.Bijective (![i, j, k] : Fin 3 → Fin 3) then
    (((Equiv.Perm.sign (Equiv.ofBijective (![i, j, k] : Fin 3 → Fin 3) hijk) : ℤˣ) : ℤ) : ℂ)
  else 0
def PauliMatrixRelations : Prop :=
  (∀ i j : Fin 3, ComplexMatrix2.pauliFamily i * ComplexMatrix2.pauliFamily j =
    (if i = j then (1 : ComplexMatrix2) else 0) +
      Complex.I • ∑ k, leviCivitaSymbol i j k • ComplexMatrix2.pauliFamily k) ∧
  (∀ i j : Fin 3, ComplexMatrix2.pauliFamily i * ComplexMatrix2.pauliFamily j -
      ComplexMatrix2.pauliFamily j * ComplexMatrix2.pauliFamily i =
    (2 * Complex.I) • ∑ k, leviCivitaSymbol i j k • ComplexMatrix2.pauliFamily k) ∧
  (∃ b : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement,
    ∀ i, (b i).toMatrix = ComplexMatrix2.pauliFamily i) ∧
  (∃ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
    ∀ i, ((b i : ComplexMatrix2.traceless) : ComplexMatrix2) = ComplexMatrix2.pauliFamily i) ∧
  (∀ (A B : ComplexMatrix2.traceless) (u v : Fin 3 → ℂ),
    (A : ComplexMatrix2) = ∑ i, u i • ComplexMatrix2.pauliFamily i →
      (B : ComplexMatrix2) = ∑ i, v i • ComplexMatrix2.pauliFamily i →
        traceForm A B = ∑ i, u i * v i) ∧
  (∀ A : ComplexMatrix2.traceless, (A : ComplexMatrix2) ^ 2 = traceForm A A • (1 : ComplexMatrix2)) ∧
  (∀ A B : ComplexMatrix2.traceless,
    ComplexMatrix2.operatorNorm ((A : ComplexMatrix2) * (B : ComplexMatrix2) -
        (B : ComplexMatrix2) * (A : ComplexMatrix2)) ≤
      2 * ComplexMatrix2.operatorNorm (A : ComplexMatrix2) *
        ComplexMatrix2.operatorNorm (B : ComplexMatrix2)) ∧
  (∀ A : ComplexMatrix2.traceless, (A : ComplexMatrix2) ∈ ComplexMatrix2.hermitianTraceless →
    ((ComplexMatrix2.operatorNorm (A : ComplexMatrix2) ^ 2 : ℝ) : ℂ) = traceForm A A) ∧
  (∀ B ∈ ComplexMatrix2.hermitianTraceless,
    ComplexMatrix2.halfTrace (ComplexMatrix2.matExp (Complex.I • B)) =
      ((Real.cos (ComplexMatrix2.operatorNorm B) : ℝ) : ℂ)) ∧
  (∀ (g : ComplexMatrix2.specialLinear) (A B : ComplexMatrix2.traceless),
    traceForm (ComplexMatrix2.conjugateOnTraceless (g : ComplexMatrix2) A)
        (ComplexMatrix2.conjugateOnTraceless (g : ComplexMatrix2) B) =
      traceForm A B) ∧
  (∀ g ∈ gaugeGroup, ComplexMatrix2.conjugateBy g '' (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) =
    (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2))
end OneLoop
end YangMills.Construction
end
