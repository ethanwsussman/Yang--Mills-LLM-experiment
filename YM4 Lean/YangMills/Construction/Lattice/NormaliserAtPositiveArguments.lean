import YangMills.Construction.Lattice.GaugeFixingFactor
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
def extendedAxialNormalizer (x ε : ℝ) : ℝ :=
  ∫ u : ComplexMatrix2.specialUnitary,
    nearIdentityIndicator ε (u : ComplexMatrix2) * Real.exp (-x * traceDeficit (u : ComplexMatrix2))
      ∂ComplexMatrix2.haarProb
end YangMills.Construction.PeriodicLattice
