import YangMills.Construction.ClusterExpansionOfAStep.FieldsAsConfigurations
import YangMills.Construction.ClusterExpansionOfAStep.TheFlowIsTheLawOfTheChain
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
def bottomChainLawIsWilsonGibbsStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (β : ℝ) (x : ℕ → ℝ) (t n m K : ℕ) [NeZero n]
    (D : TorusLumps.TorusFunctional),
    WeightedResponses.fineSide ℓ.side t n = 2 * ℓ.side ^ (m + K) → 2 < WeightedResponses.fineSide ℓ.side t n →
      ClusterExpansionOfAStep.IsChainDensity ℓ β x t n D →
      ClusterExpansionOfAStep.wilsonPartition β (WeightedResponses.fineSide ℓ.side t n) =
        PeriodicLattice.partitionFunction ℓ.side m K β ∧
      ∀ G : (PeriodicLattice.Bond ℓ.side m (K : ℤ) → Matrices.ComplexMatrix2) → ℝ,
        ClusterExpansionOfAStep.IsBoundedMeasurable G →
        ∫ u, G (ClusterExpansionOfAStep.gaugeFieldOfTorusField ℓ.side m (K : ℤ) (WeightedResponses.initialField ℓ t n u))
            ∂(WeightedResponses.chainJointLaw ℓ β x t n) =
          ∫ U, G U ∂(PeriodicLattice.wilsonGibbsMeasure ℓ.side m K β)
end ClusterExpansionOfAStep
end YangMills.Construction
end
