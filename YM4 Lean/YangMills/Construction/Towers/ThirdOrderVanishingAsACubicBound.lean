import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def VanishingOrderThreeIffCubicBound : Prop :=
  ∀ (O : Set (Coordinates.ComplexCoordinates 2))
    (f : Coordinates.ComplexCoordinates 2 → Coordinates.ComplexCoordinates 4),
    (0 : Coordinates.ComplexCoordinates 2) ∈ O → Coordinates.ComplexCoordinates.IsHolomorphicIn O f →
      (VanishesToOrderThree O f ↔
        ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
          ∀ z : Coordinates.ComplexCoordinates 2, ‖z‖ < δ → ‖f z‖ ≤ C * ‖z‖ ^ 3)
end YangMills.Construction.Tower
end
