import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def coldCoordinateMomentsAt (T : ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ q : ℕ, ∃ C : ℝ, ∀ (t : ℕ) (x : ℝ) (f : ColdStepAtMirrorFrames.LocalFamily) (F : BlockAverages.BlockFrame)
    (V : F.GaugeField F.top)
    (b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F))), T.coupling ≤ x →
    ColdStepAtMirrorFrames.IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    ColdStepAtMirrorFrames.IsCubicTopTorus T.L t T.n₀ F → ColdStepAtMirrorFrames.IsSmallCurvature T.σ V →
    (WeightedResponses.coldHalfLawAt T x f).expectation V (fun η => ‖η b‖ ^ (2 * q)) ≤ C * (x ^ q)⁻¹
def coldHalfLawMomentsAt (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  ∃ (c : ColdStepAtMirrorFrames.ColdChainParameters) (j : ℕ), Tb.Compatible c ∧
    coldCoordinateMomentsAt (Tb.stepParamsAt c j y)
def coldHalfLawMomentsStatement : Prop := HoldsOnParameterFamilies coldHalfLawMomentsAt
end YangMills.Construction.ResponseInTheExpansion
end
