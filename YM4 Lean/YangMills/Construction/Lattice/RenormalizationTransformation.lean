import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open MeasureTheory Set YangMills.Construction.Matrices YangMills.Construction.Averaging
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def IsFiniteGaugeMeasure (k : ℕ) (ν : Measure (BondAtLevel L m K k → ComplexMatrix2)) :
    Prop :=
  IsFiniteMeasure ν ∧ ν (gaugeFieldsAtLevel L m K k)ᶜ = 0
def rgMap (k : ℕ) (ν : Measure (BondAtLevel L m K k → ComplexMatrix2)) :
    Measure (BondAtLevel L m K (k + 1) → ComplexMatrix2) :=
  ν.map (blockAverageStep (smoothingRadius L) k)
end YangMills.Construction.PeriodicLattice
