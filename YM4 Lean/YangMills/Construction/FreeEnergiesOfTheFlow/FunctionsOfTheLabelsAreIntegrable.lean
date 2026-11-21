import YangMills.Construction.FreeEnergiesOfTheFlow.ScoresOverAStepDefs
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace FreeEnergies
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
def labelFunctionsIntegrableStatement : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (S : Finset (TorusSite (n * R.params.side)))
    (h : (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ), (∀ Yt, Measurable (h Yt)) →
    (∀ Yt ωt, |h Yt ωt| ≤ Real.exp (scoreSumOn A S Yt ωt)) →
    CaseIntegrable R G.cut G.coarse G.state fun _ Yt ωt _ _ => h Yt ωt
end FreeEnergies
end YangMills.Construction
end
