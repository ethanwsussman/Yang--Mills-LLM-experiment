import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Mathlib
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates
open PowerSeriesHolomorphy in
def BoundedHolomorphicLipschitz.Bound : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (O : Set (ComplexCoordinates n)), IsOpen O →
    ∀ (f : ComplexCoordinates n → ℂ) (b : ℝ),
      IsHolomorphicIn (N' := 1) O (fun z _ => f z) → (∀ z ∈ O, ‖f z‖ ≤ b) →
      ∀ (ρ : ℝ) (a : ComplexCoordinates n), 0 < 2 * ρ → a ∈ O → closedPolydisk a (2 * ρ) ⊆ O →
        ∀ z ∈ closedPolydisk a ρ, ∀ z' ∈ closedPolydisk a ρ,
          ‖f z - f z'‖ ≤ 2 * b / ρ * ∑ k, ‖z k - z' k‖
end YangMills.Construction.Coordinates.ComplexCoordinates
