import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ChartShiftLipschitz : Prop :=
  ∀ (F : BlockFrame) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) (r : ℝ), Odd F.blockSide → (∀ b, ‖η b‖ ≤ r) → 0 ≤ r →
    (∀ x i, ‖stepCoordinates η x i‖ ≤ r) ∧
    (∀ p : F.Site F.depth × Fin 4 × Fin 4,
      plaquetteDefect (chartedField (fun x i => w x i + stepCoordinates η x i) V) p ≤
        plaquetteDefect (chartedField w V) p + 4 * r) ∧
    ∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect (chartedField (fun x i => w x i + stepCoordinates η x i) V) V c h π - 1‖ ≤
        ‖contourHolonomyDefect (chartedField w V) V c h π - 1‖ + 5 * (F.blockSide : ℝ) * r
end YangMills.Construction.ColdStepAtMirrorFrames
end
