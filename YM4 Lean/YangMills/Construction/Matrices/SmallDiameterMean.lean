import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Matrices.SpecialUnitaryFamilyMeans
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.SmallDiameterMean
open ComplexMatrix2
variable {n : ℕ}
def leadMember (V : Fin n → ComplexMatrix2) : ComplexMatrix2 :=
  if h : 0 < n then V ⟨0, h⟩ else 1
def meanMap (V : Fin n → ComplexMatrix2) (Y : ComplexMatrix2) : ComplexMatrix2 :=
  Y + (n : ℂ)⁻¹ • ∑ i, logSeries (V i * (leadMember V)⁻¹ * matExp (-Y))
def meanFixedPt (V : Fin n → ComplexMatrix2) : ComplexMatrix2 :=
  Classical.epsilon fun Y => Y ∈ closedBallEighth ∧ meanMap V Y = Y
def average (V : Fin n → ComplexMatrix2) : ComplexMatrix2 :=
  matExp (meanFixedPt V) * leadMember V
def narrowFamilies (n : ℕ) : Set (Fin n → ComplexMatrix2) :=
  {V | (∀ i, IsUnit (V i)) ∧ unitFamilyDiameter V < 1 / 40}
def familyEquiv (n : ℕ) : (Fin n → ComplexMatrix2) ≃
    Coordinates.ComplexCoordinates (Coordinates.ComplexCoordinates.productDim
      fun _ : Fin n => Coordinates.ComplexCoordinates.Component.matrix) :=
  Coordinates.ComplexCoordinates.productEquiv fun _ => Coordinates.ComplexCoordinates.Component.matrix
def AverageStatement : Prop :=
  (∀ (n : ℕ) (V : Fin n → ComplexMatrix2), IsUnitFamily V → unitFamilyDiameter V ≤ 1 / 40 →
    (∀ Y ∈ closedBallEighth, ∀ i,
      operatorNorm (V i * (leadMember V)⁻¹ * matExp (-Y) - 1) < 1 / 6) ∧
    MapsTo (meanMap V) closedBallEighth closedBallEighth ∧
    (∀ Y ∈ closedBallEighth, ∀ Y' ∈ closedBallEighth,
      operatorNorm (meanMap V Y - meanMap V Y') ≤ 2 / 5 * operatorNorm (Y - Y')) ∧
    (∃! Y, Y ∈ closedBallEighth ∧ meanMap V Y = Y) ∧
    operatorNorm (meanFixedPt V) ≤ 2 * unitFamilyDiameter V ∧
    IsUnit (average V) ∧
    (∀ i, operatorNorm (V i * (average V)⁻¹ - 1) ≤ 4 * unitFamilyDiameter V) ∧
    4 * unitFamilyDiameter V ≤ 1 / 10 ∧
    ∑ i, logSeries (V i * (average V)⁻¹) = 0 ∧
    (∀ V' : ComplexMatrix2, IsUnit V' → (∀ i, operatorNorm (V i * V'⁻¹ - 1) < 1) →
      ∑ i, logSeries (V i * V'⁻¹) = 0 → (∃ k, operatorNorm (V k * V'⁻¹ - 1) ≤ 1 / 10) →
      V' = average V) ∧
    (∀ π : Equiv.Perm (Fin n), average (V ∘ π) = average V) ∧
    ((∀ i, V i ∈ unitDeterminant) →
      meanFixedPt V ∈ traceless ∧ average V ∈ unitDeterminant) ∧
    ((∀ i, V i ∈ specialUnitary) →
      (∃ A ∈ hermitianTraceless, meanFixedPt V = Complex.I • A) ∧ average V ∈ specialUnitary) ∧
    ((∀ i, V i ∈ specialUnitary) → ∀ V' ∈ specialUnitary,
      (∀ i, operatorNorm (V i * V'⁻¹ - 1) < 1) →
      ∑ i, logSeries (V i * V'⁻¹) = 0 → V' = average V)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ W : ComplexMatrix2, IsUnit W → average (fun _ : Fin n => W) = W) ∧
  (∀ n : ℕ, 1 ≤ n → IsOpen (narrowFamilies n) ∧
    Coordinates.ComplexCoordinates.IsHolomorphicVia (familyEquiv n)
      Coordinates.ComplexCoordinates.matrixEquiv (narrowFamilies n) meanFixedPt ∧
    Coordinates.ComplexCoordinates.IsHolomorphicVia (familyEquiv n)
      Coordinates.ComplexCoordinates.matrixEquiv (narrowFamilies n) average) ∧
  ∀ (n : ℕ) (V : Fin n → ComplexMatrix2), IsSpecialUnitaryFamily V →
    unitFamilyDiameter V ≤ 1 / 40 →
    (∀ W : ComplexMatrix2, IsSpecialUnitaryLogMean V W ↔ W = average V) ∧
    ∀ ω ∈ Ioc (4 * unitFamilyDiameter V) 1, ∀ W : ComplexMatrix2,
      IsLogMeanOfRadius ω V W ↔ W = average V
end YangMills.Construction.Matrices.SmallDiameterMean
