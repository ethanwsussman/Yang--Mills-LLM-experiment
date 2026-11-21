import YangMills.Construction.ResponseInTheExpansion.FarObservablesDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters WeightedResponses FreeEnergies Dobrushin
namespace ResponseInTheExpansion
def separatedProductOverGasStatement : Prop :=
  HoldsAtEveryStepWithConstant fun C T R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (ι : Type) (I : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (D : ℕ), I.Nonempty →
      SeparatedWeights I f D →
      Integrable (fun σ => ∏ i ∈ I, gasSupportMean A G (f i) σ) (G.gibbsLaw ∅) ∧
      (∀ i ∈ I, Integrable (gasSupportMean A G (f i)) (G.gibbsLaw ∅)) ∧
      |G.expectation ∅ (fun σ => ∏ i ∈ I, gasSupportMean A G (f i) σ) -
          ∏ i ∈ I, G.expectation ∅ (gasSupportMean A G (f i))| ≤
        C * (I.card : ℝ) ^ 2 * Real.exp (2 * I.card * Real.exp (-(7 * T.gasRate * R.coupling))) * totalLowerSites I f *
          Real.exp (-(R.params.rt * D / 2 ^ 6)) * ∏ i ∈ I, upperMajorant A G (f i)
end ResponseInTheExpansion
end YangMills.Construction
end
