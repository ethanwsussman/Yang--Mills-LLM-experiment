import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open Filter
namespace YangMills.Construction.ComplexAnalysis
open YangMills.Construction.Coordinates
def MontelSeveralVariables : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ U : Set (ComplexCoordinates n), IsOpen U →
    ∀ f : ℕ → ComplexCoordinates n → ℂ,
      (∀ j, 1 ≤ j → ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun z _ => f j z) →
      (∃ M : ℝ, ∀ j, 1 ≤ j → ∀ z ∈ U, ‖f j z‖ ≤ M) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ l, 1 ≤ φ l) ∧
        ∃ g : ComplexCoordinates n → ℂ,
          (ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun z _ => g z) ∧
          ∀ K : Set (ComplexCoordinates n), K ⊆ U → IsCompact K →
            TendstoUniformlyOn (fun l => f (φ l)) g atTop K
end YangMills.Construction.ComplexAnalysis
