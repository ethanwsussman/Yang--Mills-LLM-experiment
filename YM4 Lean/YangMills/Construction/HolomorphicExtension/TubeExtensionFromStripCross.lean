import YangMills.Construction.ComplexAnalysis.SeparatelyHolomorphicOnStrips
import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.HolomorphicExtension.HullConstants
import Mathlib
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.HolomorphicExtension
def TubeExtensionFromStripCross : Prop :=
  ∀ (n : ℕ+) (f : (Fin n → ℝ) → ℂ),
    Strips.IsSepHolomorphicOnStrips f →
    (∀ (x : Fin n → ℝ) (T w : ℝ), 0 ≤ T → 0 ≤ w → w < Real.pi / 2 →
      Strips.supOnCross f x T w < ∞) →
    ∃ F : Coordinates.ComplexCoordinates n → ℂ,
      Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (Strips.halfPiTube n)
        (fun z _ => F z) ∧
      (∀ x : Fin n → ℝ, F (fun j => (x j : ℂ)) = f x) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        HullConstants.halfWidth ε < Real.pi / 2 ∧
        ∀ x y : Fin n → ℝ, ∑ j, |y j| ≤ (1 - ε) * (Real.pi / 2) →
          ‖F (fun j => (x j : ℂ) + (y j : ℂ) * Complex.I)‖ₑ ≤
            ENNReal.ofReal (HullConstants.boundFactor n ε) *
              Strips.supOnCross f x (HullConstants.radius ε) (HullConstants.halfWidth ε)
end YangMills.Construction.HolomorphicExtension
