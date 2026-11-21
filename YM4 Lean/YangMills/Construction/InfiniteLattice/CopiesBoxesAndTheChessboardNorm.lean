import YangMills.Construction.Lattice.SourcedPartitionFunctionOfALattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def weightedPartitionFn (L m K : ℕ) (β : ℝ) (w : PeriodicLattice.FourTorus L m → ℂ) : ℂ :=
  ∫ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
    Complex.exp (-PeriodicLattice.barycenterWeightedEnergy (fun y => (β : ℂ) - w y) U.1)
      ∂PeriodicLattice.gaugeFieldMeasure L m (K : ℤ)
theorem weightedPartitionFn_eq_sourced (L m K : ℕ) (β : ℝ)
    (w : PeriodicLattice.FourTorus L m → ℂ) :
    weightedPartitionFn L m K β w =
      PeriodicLattice.sourcedPartitionFunction L m K (β : ℂ) w := rfl
end InfiniteLattice
end YangMills.Construction
end
