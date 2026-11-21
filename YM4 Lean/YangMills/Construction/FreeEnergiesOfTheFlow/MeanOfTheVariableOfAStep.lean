import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace FreeEnergies
open StepSettings StepGas StepCosts TorusFields TorusLumps RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
def supportResponseMeanStatement : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n] (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
    (∀ G : GasGround R n, G.IsAdmissibleGround →
      CaseIntegrable R G.cut G.coarse G.state (centeredSupportResponse A G.coarse f) ∧
      caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse f) =
        ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
        (caseMean R G.cut G.coarse G.state (caseResponse A G.coarse Y f) -
          caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) Y f))) ∧
    (R.params.n₀ ≤ n → weightNorm R.params.side R.depth f ≤ 1 → weightNorm R.params.side (R.depth + 1) f ≤ 1 →
      ∀ (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n),
        |R.params.coupling / 2 * A.coeff * ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
            blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V b Y -
            caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| ≤
          2 * (A.responseParams.C₀ * ((weightSupportSites R.params.side R.depth (n * R.params.side) f).card : ℝ)))
end FreeEnergies
end YangMills.Construction
end
