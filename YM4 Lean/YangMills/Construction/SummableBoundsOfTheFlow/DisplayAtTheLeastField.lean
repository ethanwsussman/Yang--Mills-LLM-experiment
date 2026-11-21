import YangMills.Construction.ColdStepAtMirrorFrames.DisplayOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames MeasureTheory
namespace Interpolation
variable {F : BlockFrame}
def logIntegralAtMinimizerStatement : Prop :=
  ∀ (F : BlockFrame) (a ρA ρ lam x M : ℝ) (m m' m₁ : ℕ) (p : ℝ → ℝ) (f : LocalFamily)
    (V : F.GaugeField F.top),
    0 ≤ a → Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → (¬ ∀ i, 4 * m₁ + 5 < F.extent i) →
    (∀ b ∈ chordBonds (finiteCells F), ‖stepFrame true a ρA m b V‖ + ρ < Real.pi) →
    IsRegularStep a ρA ρ lam x M m₁ p f V →
    Real.log (interpolatedStepIntegral 0 a ρA ρ x m p f V) =
      (∑ _c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x)) +
        (∑ _b : ↥(chordBonds (finiteCells F)), Real.log (haarRadialDensity 0)) +
        Real.log (gaussianMass ρ lam x p F) - x * minimalAction a (finiteCells F) F.top V +
        ∑ Y ∈ finiteCells F, (interactionDensity true a ρA ρ lam x m' p f Y V +
          expansionDensity true a ρA ρ x m' p f Y V + frameDensity true a ρA x m' Y V)
end Interpolation
end YangMills.Construction
end
