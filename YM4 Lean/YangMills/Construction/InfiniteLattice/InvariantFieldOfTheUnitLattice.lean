import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
abbrev unitShiftInvariantSigma : MeasurableSpace (GaugeField 1) :=
  shiftInvariantSigma 1
end YangMills.Construction.InfiniteLattice
