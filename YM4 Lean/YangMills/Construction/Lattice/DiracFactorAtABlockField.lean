import YangMills.Construction.Lattice.FibreMeasuresAndTheirProperties
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace AverageFibres
variable {L m K k : ℕ}
def diracFibreMeasure (W : PositiveBondField L m K (k + 1)) :
    Measure (PositiveBondField L m K k) :=
  fibreMeasureFamily L m K k W
end AverageFibres
end YangMills.Construction
end
