import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.ResponseInTheExpansion.LawOfTheColdHalf
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms
namespace WeightedResponses
variable {F : BlockFrame}
def coldHalfLawAt (T : StepParameters) (x : ℝ) (f : LocalFamily) : ColdHalfLaw :=
  ⟨T.a, T.chainParams.ρA, T.ballRadius, x, T.κ, frameRadius x, T.p, f⟩
def InClosedBallProduct (ρ : ℝ) (η : StepVariable (finiteCells F)) : Prop := ∀ b, ‖η b‖ ≤ ρ
structure IsAdmissibleAt (T : StepParameters) (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame)
    (V : F.GaugeField F.top) : Prop where
  coupling_le : T.coupling ≤ x
  family_bounded : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f
  torus : IsCubicTopTorus T.L t T.n₀ F
  small_curvature : IsSmallCurvature (5 / 4 * T.σ) V
end WeightedResponses
end YangMills.Construction
end
