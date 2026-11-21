import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
def topVariationAlongField : Prop :=
  ∀ (F : BlockFrame) (s a ρA ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions),
    Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → 0 < ρ → (∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th w X)) →
    (∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m b) V) →
    (∀ b ∈ chordBonds (finiteCells F), ‖interpolatedFrame s a ρA m b V‖ + ρ ≤ 1) →
    ∀ (G : F.GaugeField F.depth → ℝ) (η : StepVariable (finiteCells F)) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions),
      (∀ b, ‖η b‖ < ρ) → ContDiffThreeAlongBonds G (interpolatedField s a ρA m V η) →
      bondDeriv (fun W => G (interpolatedField s a ρA m W η)) V (fun _ : Fin 1 => c) (fun _ => X) =
        ∑ b : ↥(chordBonds (finiteCells F)), bondPartialDeriv (fun ζ => G (interpolatedField s a ρA m V ζ)) b η
          (imaginaryCoords (topVariationField Th s a ρA m c X b.1 (toImaginary (η b)) V))
end YangMills.Construction.Interpolation
end
