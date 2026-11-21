import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages
def farSupportsDecorrelateInSetting : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ y₀ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y →
    ∀ (R : StepSetup) (n : ℕ) [NeZero n] (s : ChartSetting R n), R.params.n₀ ≤ n → s.IsAdmissible →
    ∀ (bad : Finset (TorusBond (n * R.params.side))) (ι : Type) (I : Finset ι) (A : ι → ResponseSetup R)
      (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (v : ι → ℝ) (D : ℕ),
      (∀ i ∈ I, (A i).responseParams = K) → (∀ i ∈ I, OnStepParameters T y (A i)) → I.Nonempty →
      (∀ i ∈ I, weightNorm R.params.side (R.depth + 1) (f i) ≤ 1) →
      (∀ i ∈ I, (weightSupportSites R.params.side (R.depth + 1) n (f i)).Nonempty) →
      2 ^ 10 * R.range ≤ D → 8 < D →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ Y ∈ thickening 2 (weightSupportSites R.params.side (R.depth + 1) n (f i)),
        ∀ Y' ∈ thickening 2 (weightSupportSites R.params.side (R.depth + 1) n (f j)), D ≤ supDist Y Y') →
      (∀ i ∈ I, |v i| ≤ (K.C₀ + 1 + 16 * R.params.coupling) *
        ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)) →
      |weightedMean (chartDensity s) (fun η => ∏ i ∈ I,
          (supportResponseSum (A i) s.coarse (f i) (s.field η) s.support s.labelling bad s.bases - v i)) -
        ∏ i ∈ I, weightedMean (chartDensity s)
          (fun η => supportResponseSum (A i) s.coarse (f i) (s.field η) s.support s.labelling bad s.bases - v i)| ≤
      C * I.card * (∑ i ∈ I, ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)) *
        Real.exp (-(R.params.rt * D / 2 ^ 4)) *
        ∏ i ∈ I, (4 * (K.C₀ * ((weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)) *
          meanSiteScore (A i).score (weightSupportSites R.params.side R.depth (n * R.params.side) (f i))
            s.support s.labelling)
end YangMills.Construction.ResponseInTheExpansion
end
