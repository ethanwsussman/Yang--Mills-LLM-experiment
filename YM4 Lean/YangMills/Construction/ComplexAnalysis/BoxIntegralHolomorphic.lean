import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ComplexAnalysis
open Coordinates
def BoxIntegralHolomorphicInParameter : Prop :=
  ∀ (n N : ℕ), 1 ≤ n → 1 ≤ N →
    ∀ (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
      ∀ U : Set (ComplexCoordinates N), IsOpen U →
        ∀ γ : (Fin n → ℝ) → ComplexCoordinates N → ℂ,
          (∃ m : ℝ, ∀ t ∈ Icc a b, ∀ p ∈ U, ‖γ t p‖ ≤ m) →
          (∀ p ∈ U, ContinuousOn (fun t => γ t p) (Icc a b)) →
          (∀ t ∈ Icc a b, ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun p _ => γ t p) →
          ContinuousOn (Function.uncurry γ) (Icc a b ×ˢ U) ∧
            ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun p _ => ∫ t in Icc a b, γ t p
end YangMills.Construction.ComplexAnalysis
end
