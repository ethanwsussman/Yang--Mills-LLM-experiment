import YangMills.Construction.Lattice.MeanLinearAverageIsTheAbsorbedAverage
import YangMills.Construction.Lattice.ToolboxMeanLinearAverageIsTheAbsorbedAverage
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
theorem centredSchemeLinearAverageEq_of_scaled (hT : CentredLinearAverageEqScaled) :
    CentredSchemeLinearAverageEq := by
  intro L hL m K n hm hn c hc a A hA hAa
  exact (hT L hL m K n hm hn c hc a).2 A hA hAa
end YangMills.Construction.PeriodicLattice
