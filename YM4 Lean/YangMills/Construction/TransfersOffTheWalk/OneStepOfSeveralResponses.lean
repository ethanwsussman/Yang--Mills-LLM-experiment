import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedObservables
open StepSettings TorusLumps TorusFields StepGas RenormalizationStepParameters WeightedResponses BlockAverages
open YangMills.Construction.ResponseInTheExpansion
def severalResponsesStepDecorrelation : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ y₀ : ℝ, ∀ p : ℕ, ∃ C : ℝ, ∀ y : ℝ, y₀ ≤ y →
    ∀ (R : StepSetup) (A₀ : ResponseSetup R), A₀.responseParams = K → OnStepParameters T y A₀ →
    ∀ (ι : Type) (I : Finset ι) (A : ι → ResponseSetup R) (s : R.labels.Ω → ℝ),
      (∀ i ∈ I, (A i).responseParams = K) → (∀ i ∈ I, (A i).score = s) →
      (∀ i ∈ I, OnStepParameters T y (A i)) →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (D : ℕ), I.card = p →
      (∀ i ∈ I, weightNorm R.params.side (R.depth + 1) (f i) ≤ 1) →
      (∀ i ∈ I, (weightSupportSites R.params.side (R.depth + 1) n (f i)).Nonempty) →
      2 ^ 10 * R.range ≤ D → 8 < D →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ Y ∈ thickening 2 (weightSupportSites R.params.side (R.depth + 1) n (f i)),
        ∀ Y' ∈ thickening 2 (weightSupportSites R.params.side (R.depth + 1) n (f j)), D ≤ supDist Y Y') →
      CaseIntegrable R G.cut G.coarse G.state
          (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse (A i) G.coarse (f i) W Yt ωt bad b) ∧
      (∀ i ∈ I, CaseIntegrable R G.cut G.coarse G.state (centeredSupportResponse (A i) G.coarse (f i))) ∧
      |caseMean R G.cut G.coarse G.state
            (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse (A i) G.coarse (f i) W Yt ωt bad b) -
          ∏ i ∈ I, caseMean R G.cut G.coarse G.state (centeredSupportResponse (A i) G.coarse (f i))| ≤
        C * (∑ i ∈ I, ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)) ^ 2 *
          Real.exp (-(R.params.rt * D / 2 ^ 7)) *
          ∏ i ∈ I, (4 * (K.C₀ * ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)) *
            meanSiteScore (coarseLabelScore K.s₁ s) (weightSupportSites R.params.side (R.depth + 1) n (f i))
              G.state.1 G.state.2)
end YangMills.Construction.WeightedObservables
end
