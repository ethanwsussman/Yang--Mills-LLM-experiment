import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ComplexAnalysis.RealPiece
open Coordinates
def conjCoords {N : ℕ} (z : ComplexCoordinates N) : ComplexCoordinates N :=
  fun j => conj (z j)
def EqOfEqOnRealOpenAndConjHolomorphic : Prop :=
  (∀ (N N' : ℕ) (U R : Set (ComplexCoordinates N)) (f₁ f₂ : ComplexCoordinates N → ComplexCoordinates N'),
    IsOpen U → IsConnected U → ComplexCoordinates.IsHolomorphicIn U f₁ →
    ComplexCoordinates.IsHolomorphicIn U f₂ →
    R.Nonempty → R ⊆ U ∩ ComplexCoordinates.realLocus N →
    Matrices.ComplexMatrix2.IsRelativelyOpen (ComplexCoordinates.realLocus N) R → EqOn f₁ f₂ R →
    EqOn f₁ f₂ U) ∧
  (∀ (N N' : ℕ) (U : Set (ComplexCoordinates N)) (f : ComplexCoordinates N → ComplexCoordinates N'),
    IsOpen U → MapsTo conjCoords U U → ComplexCoordinates.IsHolomorphicIn U f →
    ComplexCoordinates.IsHolomorphicIn U fun z => conjCoords (f (conjCoords z)))
end YangMills.Construction.ComplexAnalysis.RealPiece
