import YangMills.Construction.ResponseInTheExpansion.FarObservablesDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters WeightedResponses FreeEnergies Dobrushin
namespace ResponseInTheExpansion
def separatedProductOverStepStatement : Prop :=
  HoldsAtEveryStepWithConstant fun C T R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (ι : Type) (I : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (D : ℕ), I.Nonempty →
      SeparatedWeights I f D →
      CaseIntegrable R G.cut G.coarse G.state
        (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse A G.coarse (f i) W Yt ωt bad b) ∧
      |caseMean R G.cut G.coarse G.state
          (fun W Yt ωt bad b => ∏ i ∈ I, centeredSupportResponse A G.coarse (f i) W Yt ωt bad b) -
          ∏ i ∈ I, caseMean R G.cut G.coarse G.state (centeredSupportResponse A G.coarse (f i))| ≤
        C * (I.card : ℝ) ^ 2 * Real.exp (2 * I.card * Real.exp (-(7 * T.gasRate * R.coupling))) * totalLowerSites I f *
          Real.exp (-(R.params.rt * D / 2 ^ 6)) * ∏ i ∈ I, upperMajorant A G (f i)
end ResponseInTheExpansion
end YangMills.Construction
end
