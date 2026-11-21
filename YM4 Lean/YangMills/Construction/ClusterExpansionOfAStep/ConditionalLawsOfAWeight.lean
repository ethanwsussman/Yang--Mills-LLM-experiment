import YangMills.Construction.ClusterExpansionOfAStep.LawOfAWeightOnSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
namespace Dobrushin
def ActivityConditionalLawsStatement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, MeasurableSpace (S i)] (A : PairConstraint S)
    (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)] (G : (∀ i, S i) → ℝ) (z : I → ℝ)
    (hG : A.IsActivityBounded m G z),
    IsProbabilityMeasure (A.gibbsLaw m G) ∧
    A.IsSpecification (A.gibbsLaw m G) (A.singleSiteKernel m hG.measurable_weightDensity) ∧
    (∀ i σ, A.IsAdmissible σ → (A.singleSiteKernel m hG.measurable_weightDensity i σ).real {A.vacant i}ᶜ ≤ z i) ∧
    ∀ i, (A.gibbsLaw m G).real {σ | σ i ≠ A.vacant i} ≤ z i
end Dobrushin
end YangMills.Construction
end
