import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreTameMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.ScaledVariables
def lawExponentDecompositionStatement : Prop :=
  ∀ (F : BlockFrame) (a ρ lam l : ℝ) (f : LocalFamily) (law : StepLaw) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)), Finite F.Cell →
    rescaledLawExponent a ρ lam f l V law ζ =
      remainderCoefficient law * ∑ Y ∈ finiteCells F, rescaledCellRemainder a ρ lam l Y V ζ +
        lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 -
        expansionCoefficient law * ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρ f l Y V ζ
end YangMills.Construction.ScaledVariables
end
