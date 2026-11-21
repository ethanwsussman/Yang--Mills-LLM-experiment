import YangMills.Construction.ResponseInTheExpansion.TotalOfTheResponseFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings RenormalizationStepParameters StepCosts TorusLumps TorusFields BlockAverages ColdStepAtMirrorFrames WeightedResponses
variable {R : StepSetup}
def blockConstantTerm (A : ResponseSetup R) (n : ℕ) (Y : TorusSite n) : ℝ :=
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    ∑ y ∈ TorusLumps.sitesInBlocks R.params.side {Y},
      A.cold (n * R.params.side) y (trivialField (n * R.params.side)) (constOneWeight _) - 6 * A.coeff / R.coupling
def imageOfOneAtBlockStatement : Prop :=
  HoldsAtEveryStep fun T R A => T.ColdStepHolds → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (Y : TorusSite n) (V : TorusField n), IsCold R.params.threshold V →
      A.coldStep n Y V (constOneWeight _) =
        A.coeff * levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V +
        frameTerm A n Y V + incrementTerm A n Y V +
        densityOfTopFamily R.params.side R.depth (blockConditionalMean R A.siteRemainder) n Y V +
        scoreTailTerm A n Y V + gasTerm A n Y V + blockConstantTerm A n Y
end YangMills.Construction.ResponseInTheExpansion
end
