import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def segmentEnd (star : Bool) : ℝ := if star then 0 else 1
def interpolationAtEndpoints : Prop :=
  ∀ (F : BlockFrame) (star : Bool) (a ρA lam x τ : ℝ) (m : ℕ) (V : F.GaugeField F.top),
    (∀ b, interpolatedFrame (segmentEnd star) a ρA m b V = stepFrame star a ρA m b V) ∧
    (∀ η, interpolatedCoords (segmentEnd star) a ρA m V η = coordsAboveFrame star a ρA m V η) ∧
    (∀ η, interpolatedField (segmentEnd star) a ρA m V η = fieldAboveFrame star a ρA m V η) ∧
    (∀ (f : LocalFamily) y η, interpolatedExpansion (segmentEnd star) a ρA m f y η V = centredExpansion star a ρA m f y η V) ∧
    (∀ Y η, interpolatedBlockExponent (segmentEnd star) a ρA x m Y V η = cellExponent star a ρA x m Y V η) ∧
    (∀ (f : LocalFamily) η, familyLawExponent (segmentEnd star) a ρA x m f V η =
      stepExponent star a ρA x m f 1 V η) ∧
    (∀ (f : LocalFamily) η, weightLawExponent (segmentEnd star) a ρA lam x m τ V η =
      τ * stepExponent star a ρA x m f 0 V η + (1 - τ) * totalQuadratic lam x η)
end Interpolation
end
end YangMills.Construction
