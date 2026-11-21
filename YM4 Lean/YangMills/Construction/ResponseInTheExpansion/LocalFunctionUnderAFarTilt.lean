import YangMills.Construction.ResponseInTheExpansion.FarObservablesDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusLumps TorusFields RenormalizationStepParameters StepSettings StepGas WeightedResponses FreeEnergies
def nearBlockCost (R : StepSetup) : ℝ :=
  Real.exp (R.params.rt / 2 ^ 6 * (10 * (R.range : ℝ) / R.params.side + 8))
def localFunctionFarTiltStatement : Prop :=
  HoldsAtEveryStepWithConstant fun C T R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (Y : TorusSite n) (Q : Finset (TorusSite n)) (B : Finset (TorusSite (n * R.params.side))) (e : ℝ)
      (W : G.Config → ℝ) (D : ℕ) (H : G.Config → ℝ) (M : ℝ), 2 ^ 10 * R.range ≤ D → Q.Nonempty →
      (∀ Y' ∈ Q, D ≤ supDist Y Y') → 1 ≤ e →
      IsGasTilt G A.score Q B e W → Measurable H → 0 ≤ M → (∀ σ, |H σ| ≤ 2 * M) →
      G.pairConstraint.OscillationBound H (fun i => 4 * M * nearBlockCost R * decayFromSet G {Y} i) →
      |∫ σ, H σ ∂(tiltedGibbsLaw G W) - G.expectation ∅ H| ≤
        C * M * e * (Q.card : ℝ) * Real.exp (-(6 * T.gasRate * R.coupling) - R.params.rt * D / 2 ^ 6)
end YangMills.Construction.ResponseInTheExpansion
end
