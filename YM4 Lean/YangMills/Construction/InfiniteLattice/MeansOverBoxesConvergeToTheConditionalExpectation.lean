import YangMills.Construction.InfiniteLattice.RationalPolynomialsInTheEntriesAndMeansOverBoxes
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def MeanErgodicStatement : Prop :=
  ∀ L K : ℕ, Odd L → 13 ≤ L → 0 < K →
    ∀ ν : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)),
      IsShiftInvariant ν.1 →
        ∀ F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ, IsBoundedObservable F →
          Tendsto
            (fun n : ℕ => stateL2Norm ν fun U =>
              cornerCubeAverage n F U - condExpShiftInvariant ν.1 F U)
            atTop (𝓝 0)
end YangMills.Construction.InfiniteLattice
