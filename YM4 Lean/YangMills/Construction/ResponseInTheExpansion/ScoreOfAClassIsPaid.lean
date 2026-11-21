import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open Dobrushin StepGas TorusLumps WeightedResponses
def clusterScoreIntegralBound : Prop :=
  HoldsAtEveryStep fun T R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
    ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (clusterWeight R.params.side T.gasRate R.coupling R.range i.1) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))
end YangMills.Construction.ResponseInTheExpansion
end
