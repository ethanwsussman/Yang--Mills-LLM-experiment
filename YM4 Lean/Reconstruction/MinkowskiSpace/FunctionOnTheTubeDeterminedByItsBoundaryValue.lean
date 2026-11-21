import Reconstruction.MinkowskiSpace.BoundaryValuesOnTheTube
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TubeUniqueness
def BoundaryValueDetermines : Prop :=
  ∀ (b q : ℕ) (c : ℝ) (u : (Fin b → MinkowskiSpace.ComplexVec4) → ℂ)
    (φ : ℕ → TestSpaces.PointTuple b → ℝ), 0 < b →
    WightmanTheory.IsHolomorphicOnTube u →
    (∀ ζ ∈ WightmanTheory.tubeTuples b,
      ‖u ζ‖ ≤ c * ∏ k, (min 1 (MinkowskiSpace.tubeGap (ζ k)))⁻¹ ^ q) →
    (∀ j : ℕ, 0 < j → φ j ∈ TestSpaces.smoothCompactSupp Set.univ) →
    (∀ j : ℕ, 0 < j → ∀ x, 0 ≤ φ j x) →
    (∀ j : ℕ, 0 < j → ∫ x, φ j x = 1) →
    (∀ j : ℕ, 0 < j → ∀ x, 1 / (j : ℝ) ≤ TestSpaces.tupleNorm x → φ j x = 0) →
    (∀ j : ℕ, 0 < j → ∀ a : TestSpaces.PointTuple b,
      TubeBoundary.boundaryValue u 0 (TubeBoundary.translateBy a fun x => (φ j x : ℂ)) = 0) →
    ∀ ζ ∈ WightmanTheory.tubeTuples b, u ζ = 0
end YangMills.Construction.TubeUniqueness
