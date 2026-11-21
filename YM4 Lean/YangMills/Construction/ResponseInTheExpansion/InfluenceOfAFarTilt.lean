import YangMills.Construction.ResponseInTheExpansion.FarObservablesDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open StepGas StepSettings RenormalizationStepParameters TorusFields TorusLumps FreeEnergies WeightedResponses
def farTiltInfluenceStatement : Prop :=
  HoldsAtEveryStepWithConstant fun C T R _ => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (S Q : Finset (TorusSite n)) (ε : ℝ) (D : ℕ), S.Nonempty → Q.Nonempty → 1 ≤ ε → 2 ^ 10 * R.range ≤ D →
      (∀ Y ∈ S, ∀ Y' ∈ Q, D ≤ supDist Y Y') →
      ∑ i : G.GasSpin, decayFromSet G S i * tiltActivity G T.gasRate ε Q i ≤
        C * ε * (Q.card : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling) - R.params.rt / 2 ^ 6 * D)
end YangMills.Construction.ResponseInTheExpansion
end
