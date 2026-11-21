import YangMills.Construction.ColdStepAtMirrorFrames.DisplayOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps
def stepIntegralDependsOnlyOnFunctional : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) (f f' : LocalDensity)
    (F : BlockFrame) (ρA ρ : ℝ) (m : ℕ) (p : ℝ → ℝ)
    (V : F.GaugeField F.top), ℓ.Admissible → ColdExpansion ℓ t x D f → ColdExpansion ℓ t x D f' →
    IsCubicTorusAbove ℓ.side t ℓ.n₀ F →
    Odd F.blockSide → (∀ i, 0 < F.extent i) →
    (∀ b ∈ chordBonds (finiteCells F), ‖stepFrame false ℓ.coupling ρA m b V‖ + ρ < Real.pi) →
    (∀ η : StepVariable (finiteCells F), η ∈ openBallProduct F ρ →
      IsSmallCurvature ℓ.threshold (fieldAboveFrame false ℓ.coupling ρA m V η)) →
    stepIntegral ℓ.coupling ρA ρ x m p (localFamilyOfDensity f) (finiteCells F) V =
      stepIntegral ℓ.coupling ρA ρ x m p (localFamilyOfDensity f') (finiteCells F) V
end YangMills.Construction.ColdStepAtMirrorFrames
end
