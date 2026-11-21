import YangMills.Construction.ResponseInTheExpansion.FarObservablesDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters WeightedResponses FreeEnergies Dobrushin
namespace ResponseInTheExpansion
def separatedMeanUnderTiltStatement : Prop :=
  HoldsAtEveryStepWithConstant fun C _ R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (Q : Finset (TorusSite n))
      (B : Finset (TorusSite (n * R.params.side))) (e : ℝ) (Yt : G.Config → ℝ) (D : ℕ),
      weightNorm R.params.side R.depth f ≤ 1 → (upperSites f).Nonempty →
      2 ^ 10 * R.range ≤ D → 8 < D → Q.Nonempty → (∀ Y ∈ upperSites f, ∀ Y' ∈ Q, D ≤ supDist Y Y') →
      (∀ y ∈ lowerSites f, y ∉ B) → 1 ≤ e → IsGasTilt G A.score Q B e Yt →
      Integrable (gasSupportMean A G f) (tiltedGibbsLaw G Yt) ∧ Integrable (gasSupportMean A G f) (G.gibbsLaw ∅) ∧
      |∫ σ, gasSupportMean A G f σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (gasSupportMean A G f)| ≤
        C * e * (Q.card : ℝ) * lowerSizeConst A f *
          meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 *
          Real.exp (-(R.params.rt * D / 2 ^ 6))
end ResponseInTheExpansion
end YangMills.Construction
end
