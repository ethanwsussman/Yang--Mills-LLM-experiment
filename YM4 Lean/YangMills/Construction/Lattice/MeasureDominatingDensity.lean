import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
abbrev haarMeasureAtLevel (L m K k : ℕ) : Measure (BondAtLevel L m K k → Matrices.ComplexMatrix2) :=
  productHaarMeasure L m (levelDepth K k)
end YangMills.Construction.PeriodicLattice
