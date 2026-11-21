import YangMills.Construction.ResponseInTheExpansion.FarObservablesDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepGas RenormalizationStepParameters Dobrushin
def separatedWeightTiltsStatement : Prop :=
  HoldsAtEveryStep fun T R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (ι : Type) (I J : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (D : ℕ),
    SeparatedWeights I f D → J ⊆ I → J.Nonempty →
    ∀ Y : G.Config → ℝ, (Y = (fun σ => 2 * gasMajorantProduct A G f J σ + gasMeanProduct A G f J σ) ∨
        Y = fun σ => 2 * gasMajorantProduct A G f J σ) →
      IsGasTilt G A.score (unionUpperSites f J) (unionLowerSites f J) (J.card : ℝ) Y ∧
      ∃ (hG : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate))
        (hY : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Y σ)
          fun i => 3 * G.spinActivity T.gasRate i),
        ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ → ∀ B, MeasurableSet B →
          2 * |(G.pairConstraint.singleSiteKernel (G.referenceMeasure ∅) hG.measurable_weightDensity i σ).real B -
              (G.pairConstraint.singleSiteKernel (G.referenceMeasure ∅) hY.measurable_weightDensity i σ).real B| ≤
            tiltActivity G T.gasRate (J.card : ℝ) (unionUpperSites f J) i
end YangMills.Construction.ResponseInTheExpansion
end
