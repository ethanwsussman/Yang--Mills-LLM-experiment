import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def ExpansionSecondDerivFlatAt (T : StepParameters) : Prop :=
  ∀ (t m : ℕ) (f : LocalFamily) (F : BlockFrame),
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsCubicTopTorus T.L t T.n₀ F →
    ∀ (Y : F.Cell) (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv (cellCentredExpansion true T.a T.chainParams.ρA m f Y 0) (uniformField F F.top) c X| ≤
        (T.L : ℝ) ^ (-(1 / 4 : ℝ)) * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c)
def ExpansionSecondDerivFlat : Prop := EventuallyInParameters ExpansionSecondDerivFlatAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
