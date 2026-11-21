import YangMills.Construction.ComplexAnalysis.RealPieceIdentity
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.ComplexAnalysis
open YangMills.Construction.Coordinates
def IdentityTheoremOnRealLocus : Prop :=
  (∀ (n : ℕ), 1 ≤ n → ∀ (D : Set (ComplexCoordinates n)) (f : ComplexCoordinates n → ℂ),
    IsOpen D → IsConnected D → ComplexCoordinates.IsHolomorphicIn (N' := 1) D (fun z _ => f z) →
    ∀ E : Set (ComplexCoordinates n), E.Nonempty → E ⊆ D ∩ ComplexCoordinates.realLocus n →
      Matrices.ComplexMatrix2.IsRelativelyOpen (ComplexCoordinates.realLocus n) E →
      (∀ z ∈ E, f z = 0) → ∀ z ∈ D, f z = 0) ∧
  (∀ (n₁ n₂ : ℕ), 1 ≤ n₁ → 1 ≤ n₂ →
    ∀ (D₁ : Set (ComplexCoordinates n₁)) (D₂ : Set (ComplexCoordinates n₂))
      (f : ComplexCoordinates n₁ × ComplexCoordinates n₂ → ℂ),
    IsOpen D₁ → IsConnected D₁ → IsOpen D₂ → IsConnected D₂ →
    MapsTo RealPiece.conjCoords D₁ D₁ →
    (∀ w ∈ D₂, ComplexCoordinates.IsHolomorphicIn (N' := 1) D₁
      (fun z _ => f (RealPiece.conjCoords z, w))) →
    (∀ z ∈ D₁, ComplexCoordinates.IsHolomorphicIn (N' := 1) D₂ (fun w _ => f (z, w))) →
    ∀ E : Set (ComplexCoordinates n₁ × ComplexCoordinates n₂), E.Nonempty →
      E ⊆ (D₁ ×ˢ D₂) ∩ (ComplexCoordinates.realLocus n₁ ×ˢ ComplexCoordinates.realLocus n₂) →
      Matrices.ComplexMatrix2.IsRelativelyOpen
        (ComplexCoordinates.realLocus n₁ ×ˢ ComplexCoordinates.realLocus n₂) E →
      (∀ p ∈ E, f p = 0) →
      ∀ p ∈ D₁ ×ˢ D₂, f p = 0)
end YangMills.Construction.ComplexAnalysis
