import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.RepresentativeOfASeparatedTupleCentredAtAState
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CenteredRepresentatives
open DisjointTuples
def EntriesAreLocal.Statement : Prop :=
  ∀ L K : ℕ, 0 < L → ∀ μ : Measure (InfiniteLattice.GaugeFieldAtScale L K),
    IsProbabilityMeasure μ → ∀ T : DisjointTuple,
      (∀ f ∈ T.1, f ∈ InfiniteLattice.compactTestFunctions ∧
        {p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)) |
          f p.center ≠ 0}.Finite ∧
        Integrable (InfiniteLattice.smearedEnergy f) μ ∧
        InfiniteLattice.IsBoundedObservable
          (fun U : InfiniteLattice.GaugeFieldAtScale L K =>
            ((InfiniteLattice.smearedEnergy f U : ℝ) : ℂ)) ∧
        InfiniteLattice.IsLocalObservable
          (fun U : InfiniteLattice.GaugeFieldAtScale L K =>
            ((InfiniteLattice.smearedEnergy f U : ℝ) : ℂ))) ∧
      InfiniteLattice.IsBoundedObservable (centeredRepObs L K μ T) ∧
      InfiniteLattice.IsLocalObservable (centeredRepObs L K μ T)
end YangMills.Construction.CenteredRepresentatives
