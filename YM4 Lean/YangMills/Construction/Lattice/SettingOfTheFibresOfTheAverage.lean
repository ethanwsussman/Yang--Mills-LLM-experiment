import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.LargeFieldOperation.MeasuresAndExponentOfAOneStepOperation
import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set PeriodicLattice Matrices
namespace AverageFibres
abbrev PositiveBondField (L m K j : ℕ) : Type :=
  PositivelyOrientedBond L m (levelDepth K j) → ComplexMatrix2.specialUnitary
def blockAverageMap {L m K : ℕ} (k : ℕ) (v : PositiveBondField L m K k) :
    PositiveBondField L m K (k + 1) :=
  open Classical in fun c =>
    if h : blockAverageStep (K := K) (Averaging.smoothingRadius L) k (gaugeFieldOfPositive v) c.1 ∈
        ComplexMatrix2.specialUnitary
    then ⟨_, h⟩ else 1
abbrev RealLieForm (L m K j : ℕ) : Type :=
  PositivelyOrientedBond L m (levelDepth K j) → ComplexMatrix2.LieElement
def complexify {ι : Type} (a : ι → ComplexMatrix2.LieElement) : ι → ↥ComplexMatrix2.traceless :=
  fun i => ⟨(a i).toMatrix, (Subtype.property (p := (· ∈ ComplexMatrix2.hermitianTraceless)) (a i)).2⟩
abbrev realLieFormMeasure (L m K j : ℕ) : Measure (RealLieForm L m K j) :=
  LargeField.lieLebesguePi (PositivelyOrientedBond L m (levelDepth K j))
end AverageFibres
end YangMills.Construction
end
