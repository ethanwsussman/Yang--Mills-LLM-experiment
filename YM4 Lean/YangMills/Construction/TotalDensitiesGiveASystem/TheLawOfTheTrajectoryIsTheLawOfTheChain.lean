import YangMills.Construction.ClusterExpansionOfAStep.FieldsAsConfigurations
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def FlowStartsFromLatticeAt (p : TorusLumps.StepParameters) : Prop :=
  ∀ (β : ℝ) (t n m K : ℕ) [NeZero n], WeightedResponses.fineSide p.side t n = 2 * p.side ^ (m + K) →
    2 < WeightedResponses.fineSide p.side t n →
      ClusterExpansionOfAStep.wilsonPartition β (WeightedResponses.fineSide p.side t n) =
          PeriodicLattice.partitionFunction p.side m K β ∧
      ∀ G : (PeriodicLattice.Bond p.side m (K : ℤ) → Matrices.ComplexMatrix2) → ℝ,
        ClusterExpansionOfAStep.IsBoundedMeasurable G →
        ∫ u, G (ClusterExpansionOfAStep.gaugeFieldOfTorusField p.side m (K : ℤ) (WeightedResponses.initialField p t n u))
            ∂(WeightedResponses.chainJointLaw p β (ClusterExpansionOfAStep.flowCoupling p β) t n) =
          ∫ U, G U ∂(PeriodicLattice.wilsonGibbsMeasure p.side m K β)
structure FlowIsChainLaw (p : TorusLumps.StepParameters) : Prop where
  chain_law : ∀ β : ℝ, ClusterExpansionOfAStep.FlowIsChainLawAt p β
  from_lattice : FlowStartsFromLatticeAt p
  has_expansion : ∀ β : ℝ, p.y₁ ≤ β → ClusterExpansionOfAStep.FlowHasExpansionAt p β
  read_off : ∀ β : ℝ, p.y₁ ≤ β → ClusterExpansionOfAStep.FlowReadOffAt p β
  unique : ∀ β : ℝ, p.y₁ ≤ β → ClusterExpansionOfAStep.FlowUniqueAt p β
def flowIsChainLaw : Prop :=
  HoldsAtAdmissibleParameters fun T y =>
    T.floorMin ≤ y ∧ (T.stepParameters y).Admissible ∧ FlowIsChainLaw (T.stepParameters y)
end YangMills.Construction.TotalDensities
end
