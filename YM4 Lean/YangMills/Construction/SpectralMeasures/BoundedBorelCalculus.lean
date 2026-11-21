import YangMills.Construction.SpectralMeasures.EuclideanComplexMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanBorel
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
def IsCrossIntegralOperator (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ)
    (B : H →L[ℂ] H) : Prop :=
  ∀ φ ψ : H, ⟪φ, B ψ⟫_ℂ = complexIntegral (crossForm E φ ψ) f
def IsDiagonalIntegralOperator (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ)
    (B : H →L[ℂ] H) : Prop :=
  ∀ ψ : H, ⟪ψ, B ψ⟫_ℂ = ∫ y, f y ∂(diagonalMeasure E ψ)
def boundedCalculus (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) : H →L[ℂ] H :=
  Classical.epsilon (IsCrossIntegralOperator E f)
def DiagonalMeasureProperties (E : BorelSubset n → H →L[ℂ] H) : Prop :=
  (∀ (ψ : H) (Δ : BorelSubset n), diagonalForm E ψ Δ = ((‖E Δ ψ‖ ^ 2 : ℝ) : ℂ)) ∧
  (∀ (ψ : H) (Δ : BorelSubset n), diagonalMeasure E ψ Δ.1 = ENNReal.ofReal (‖E Δ ψ‖ ^ 2)) ∧
  (∀ ψ : H, diagonalMeasure E ψ Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2)) ∧
  (∀ (c : ℂ) (ψ : H), diagonalMeasure E (c • ψ) = ENNReal.ofReal (‖c‖ ^ 2) • diagonalMeasure E ψ) ∧
  (∀ (φ ψ : H) (Δ : BorelSubset n),
    diagonalMeasure E (φ + ψ) Δ.1 ≤ 2 * diagonalMeasure E φ Δ.1 + 2 * diagonalMeasure E ψ Δ.1) ∧
  ∀ (ψ : H) (Δ Δ' : BorelSubset n),
    diagonalMeasure E (E Δ' ψ) Δ.1 = diagonalMeasure E ψ (Δ ∩ Δ').1
def NullProperties (E : BorelSubset n → H →L[ℂ] H) : Prop :=
  (∀ Δ : BorelSubset n, IsNull E Δ ↔ ∀ ψ : H, diagonalMeasure E ψ Δ.1 = 0) ∧
  (∀ Δ Δ' : BorelSubset n, Δ'.1 ⊆ Δ.1 → IsNull E Δ → IsNull E Δ') ∧
  ∀ (S : Set (BorelSubset n)) (U : BorelSubset n), S.Countable → (∀ Δ ∈ S, IsNull E Δ) →
    U.1 = ⋃ Δ ∈ S, Δ.1 → IsNull E U
def CrossFormProperties (E : BorelSubset n → H →L[ℂ] H) : Prop :=
  (∀ φ ψ : H, IsFiniteCombinationMeasure (crossForm E φ ψ)) ∧
  (∀ (φ ψ : H) (Δ : BorelSubset n), crossForm E φ ψ Δ =
    (1 / 4 : ℂ) * ∑ α ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ),
      conj α * diagonalForm E (φ + α • ψ) Δ) ∧
  ∀ (φ ψ : H) (Δ : BorelSubset n), conj (crossForm E φ ψ Δ) = crossForm E ψ φ Δ
def BoundedCalculusUnique (E : BorelSubset n → H →L[ℂ] H) : Prop :=
  ∀ f : Space n → ℂ, IsBoundedMeasurableFn f →
    IsCrossIntegralOperator E f (boundedCalculus E f) ∧
    (∀ B : H →L[ℂ] H, IsCrossIntegralOperator E f B → B = boundedCalculus E f) ∧
    IsDiagonalIntegralOperator E f (boundedCalculus E f) ∧
    ∀ B : H →L[ℂ] H, IsDiagonalIntegralOperator E f B → B = boundedCalculus E f
def BoundedCalculusProperties (E : BorelSubset n → H →L[ℂ] H) : Prop :=
  (∀ (f g : Space n → ℂ) (c : ℂ), IsBoundedMeasurableFn f → IsBoundedMeasurableFn g →
    boundedCalculus E (fun y => f y + c * g y) = boundedCalculus E f + c • boundedCalculus E g ∧
    boundedCalculus E (fun y => f y * g y) = boundedCalculus E f * boundedCalculus E g) ∧
  (∀ f : Space n → ℂ, IsBoundedMeasurableFn f → ∀ φ ψ : H,
    ⟪φ, boundedCalculus E f ψ⟫_ℂ = ⟪boundedCalculus E (fun y => conj (f y)) φ, ψ⟫_ℂ) ∧
  (∀ Δ : BorelSubset n, boundedCalculus E (Δ.1.indicator fun _ => (1 : ℂ)) = E Δ) ∧
  ∀ f : Space n → ℂ, IsBoundedMeasurableFn f → ∀ ψ : H,
    ‖boundedCalculus E f ψ‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂(diagonalMeasure E ψ)
def CutoffsConverge (E : BorelSubset n → H →L[ℂ] H) : Prop :=
  (∀ f : Space n → ℂ, Measurable f → ∀ ψ ∈ sqIntegrableDomain E f,
    ∃ v : H, Tendsto (fun k : ℕ => boundedCalculus E (cutoff f k) ψ) atTop (𝓝 v)) ∧
  ∀ f : Space n → ℂ, IsBoundedMeasurableFn f →
    sqIntegrableDomain E f = Set.univ ∧
    ∀ ψ : H, Tendsto (fun k : ℕ => boundedCalculus E (cutoff f k) ψ) atTop
      (𝓝 (boundedCalculus E f ψ))
end Operators
def BoundedBorelCalculusTheorem : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (E : BorelSubset n → H →L[ℂ] H), IsPVM E →
      DiagonalMeasureProperties E ∧ NullProperties E ∧ CrossFormProperties E ∧
      BoundedCalculusUnique E ∧ BoundedCalculusProperties E ∧ CutoffsConverge E
end YangMills.Construction.EuclideanBorel
