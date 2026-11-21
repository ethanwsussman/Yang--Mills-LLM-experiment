import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShifts
import YangMills.Construction.SummableBoundsOfTheFlow.MeanInTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Estimates
open BlockAverages ColdStepAtMirrorFrames
def conditionalExpansionMeanInvariantStatement : Prop :=
  ∀ (F : BlockFrame) (star : Bool) (a ρA x ρ : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ h : LocalFamily)
    (V : F.GaugeField F.top) (σ : ℝ),
    ChartEquivariance F a →
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      IsSmallCurvature σ (fieldAboveFrame star a ρA m V η)) →
    0 < σ →
    ((∀ (y : F.Site F.depth) (W : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion),
        IsSmallCurvature σ W → φ F y (gaugeTransform γ W) = φ F y W) ∧
      ∀ (y v : F.Site F.depth) (W : F.GaugeField F.depth), IsSmallCurvature σ W →
        φ F (y + v) (translateField v W) = φ F y W) →
    ((∀ (y : F.Site F.depth) (W : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion),
        IsSmallCurvature σ W → h F y (gaugeTransform γ W) = h F y W) ∧
      ∀ (y v : F.Site F.depth) (W : F.GaugeField F.depth), IsSmallCurvature σ W →
        h F (y + v) (translateField v W) = h F y W) →
    (∀ (γ : F.Cell → UnitQuaternion) (Y : F.Cell),
      (∀ b ∈ chordBonds (finiteCells F), stepFrame star a ρA m b (gaugeTransform γ V) =
        adjointAction (γ (enclosingCell b.1)) (stepFrame star a ρA m b V)) →
      conditionalExpansionMean star a ρA ρ x m p φ h F Y (gaugeTransform γ V) =
        conditionalExpansionMean star a ρA ρ x m p φ h F Y V) ∧
    ∀ (Y v : F.Cell),
      (∀ b ∈ chordBonds (finiteCells F),
        stepFrame star a ρA m (b.1 + cellCentre F.depth v, b.2) (translateField v V) =
          stepFrame star a ρA m b V) →
      conditionalExpansionMean star a ρA ρ x m p φ h F (Y + v) (translateField v V) =
        conditionalExpansionMean star a ρA ρ x m p φ h F Y V
end YangMills.Construction.Estimates
end
