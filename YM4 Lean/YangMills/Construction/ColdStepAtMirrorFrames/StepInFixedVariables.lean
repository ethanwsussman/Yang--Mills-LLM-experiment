import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
def stepIntegralInFixedVariables : Prop :=
  ∀ (F : BlockFrame) (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily) (V : F.GaugeField F.top),
    Odd F.blockSide → (∀ i, 0 < F.extent i) →
    (∀ b ∈ chordBonds (finiteCells F), ‖stepFrame false a ρA m b V‖ + ρ < Real.pi) →
    stepIntegral a ρA ρ x m p f (finiteCells F) V =
      Real.exp (∑ _c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x)) *
        (∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0) *
        Real.exp (- x * chartedEnergy a (coordsAboveFrame false a ρA m V 0) V) *
        ∫ η : StepVariable (finiteCells F),
          cutoffWeight ρ p η * Real.exp (- stepExponent false a ρA x m f 1 V η)
end YangMills.Construction.ColdStepAtMirrorFrames
end
