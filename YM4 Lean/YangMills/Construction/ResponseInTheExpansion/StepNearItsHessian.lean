import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.ResponseInTheExpansion.LawNearAHessian
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames
def StepNearHessianAt (T : StepParameters) : Prop :=
  ∃ Dc W K₀ Ci S : ℝ, 0 ≤ Dc ∧ 0 ≤ W ∧ 0 ≤ K₀ ∧ 0 ≤ Ci ∧ 0 ≤ S ∧
    ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
      IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (9 / 8 * T.σ) V →
      1 ≤ x ∧
      ContDiffAt ℝ 3
        (chartedEnergyAt T.a (frameCoordField false T.a T.chainParams.ρA (frameRadius x) V) V) 0 ∧
      LinearResponse.IsNearHessian T.ballRadius T.chainParams.lam x T.κ Dc W K₀ Ci S (chordBondDist F)
        (fun b b' => Real.exp (-(T.chainParams.δ₁ / 2 * chordBondDist F b b')))
        (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f 1 V)
        (LinearResponse.bondCoordinateHessian
          (chartedEnergyAt T.a (frameCoordField false T.a T.chainParams.ρA (frameRadius x) V) V))
def StepNearHessian : Prop := EventuallyInParameters StepNearHessianAt
end YangMills.Construction.ResponseInTheExpansion
end
