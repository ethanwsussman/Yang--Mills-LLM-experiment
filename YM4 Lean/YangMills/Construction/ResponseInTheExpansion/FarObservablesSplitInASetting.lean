import YangMills.Construction.ResponseInTheExpansion.FarObservablesDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters WeightedResponses FreeEnergies Dobrushin
namespace ResponseInTheExpansion
def separatedProductInChartStatement : Prop :=
  HoldsAtEveryStepWithConstant fun C _ R A => ∀ (n : ℕ) [NeZero n] (s : ChartSetting R n), R.params.n₀ ≤ n → s.IsAdmissible →
    ∀ (bad : Finset (TorusBond (n * R.params.side))) (ι : Type) (I : Finset ι)
      (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (D : ℕ),
      I.Nonempty → SeparatedWeights I f D →
      |settingMean s bad (fun W Yt ωt bad b => ∏ i ∈ I, liveCaseFunction (centeredSupportResponse A s.coarse (f i)) W Yt ωt bad b) -
          ∏ i ∈ I, settingMean s bad (liveCaseFunction (centeredSupportResponse A s.coarse (f i)))| ≤
        C * I.card * totalLowerSites I f * Real.exp (-(R.params.rt * D / 2 ^ 4)) *
          ∏ i ∈ I, lowerMajorant A (f i) s.support s.labelling
end ResponseInTheExpansion
end YangMills.Construction
end
