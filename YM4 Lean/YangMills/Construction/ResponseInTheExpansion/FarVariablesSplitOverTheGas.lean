import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages TorusFields TorusLumps StepSettings RenormalizationStepParameters StepGas FreeEnergies WeightedResponses
def GasSupportMeansDecorrelate : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ y₀ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y →
    ∀ (R : StepSetup) (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (s : R.labels.Ω → ℝ) (ι : Type) (I : Finset ι) (A : ι → ResponseSetup R)
      (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (D : ℕ), I.Nonempty →
      (∀ i ∈ I, (A i).responseParams = K) → (∀ i ∈ I, (A i).score = s) →
      (∀ i ∈ I, OnStepParameters T y (A i)) → WellSeparated I f D →
      Integrable (fun σ => ∏ i ∈ I, gasSupportMean (A i) G (f i) σ) (G.gibbsLaw ∅) ∧
      (∀ i ∈ I, Integrable (gasSupportMean (A i) G (f i)) (G.gibbsLaw ∅)) ∧
      |G.expectation ∅ (fun σ => ∏ i ∈ I, gasSupportMean (A i) G (f i) σ) -
          ∏ i ∈ I, G.expectation ∅ (gasSupportMean (A i) G (f i))| ≤
        C * (I.card : ℝ) ^ 2 * Real.exp (2 * I.card) * Real.exp (-(R.params.rt * D / 2 ^ 7)) *
          (∏ i ∈ I, (4 * (K.C₀ * ((lowerSites (f i)).card : ℝ)))) *
          ∏ i ∈ I, meanSiteScore (coarseLabelScore K.s₁ s) (upperSites (f i)) G.state.1 G.state.2
end YangMills.Construction.ResponseInTheExpansion
end
