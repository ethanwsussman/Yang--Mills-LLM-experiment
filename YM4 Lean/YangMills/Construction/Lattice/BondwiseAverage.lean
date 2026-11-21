import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
def Bond.positivelyOriented (c : Bond L m j) : Bond L m j :=
  open Classical in if c.IsPositivelyOriented then c else c.opposite
inductive BlockAverageCase
  | logarithmOfMeans
  | intrinsicLogarithmOfDefects
  | alongBond
def NoCrossingDefectIsNegOne (U : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) : Prop :=
  ∀ x ∈ sitesInBlock j' c.source, ∀ σ σ', contourCrossingDefect U c x σ σ' ≠ -1
def blockAverageCase (ω : ℝ) (U : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    BlockAverageCase :=
  open Classical in
  if IsRegularAveragingCase ω U c then .logarithmOfMeans
  else if NoCrossingDefectIsNegOne U c then .intrinsicLogarithmOfDefects
  else .alongBond
theorem blockAverageOnPositive_eq_byCase (ω : ℝ) (U : Bond L m j' → Matrices.ComplexMatrix2)
    (c : Bond L m j) :
    blockAverageOnPositive ω U c = match blockAverageCase ω U c with
      | .logarithmOfMeans => regularAverageValue U c
      | .intrinsicLogarithmOfDefects => logAverageValue U c
      | .alongBond => parallelTransport U c := by
  unfold blockAverageOnPositive blockAverageCase NoCrossingDefectIsNegOne
  split_ifs <;> rfl
structure PartialGaugeField (L m : ℕ) (j : ℤ) where
  support : Set (Bond L m j)
  field : Bond L m j → Matrices.ComplexMatrix2
def onSetElseOne (P : Set (Bond L m j')) (U : Bond L m j' → Matrices.ComplexMatrix2) :
    Bond L m j' → Matrices.ComplexMatrix2 :=
  open Classical in fun b => if b ∈ P then U b else 1
def partialBlockAverageCase (ω : ℝ) (U : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    BlockAverageCase :=
  blockAverageCase ω (onSetElseOne (bondsInDoubleBlock c) U) c.positivelyOriented
def realPartialBlockAverage (ω : ℝ) (V : PartialGaugeField L m j') : PartialGaugeField L m j where
  support := {c | bondsInDoubleBlock c ⊆ V.support}
  field := fun c => blockAverage ω (onSetElseOne (bondsInDoubleBlock c) V.field) c
def complexPartialBlockAverage (V : PartialGaugeField L m j') : PartialGaugeField L m j where
  support := {c | bondsInDoubleBlock c ⊆ V.support ∧
    onSetElseOne (bondsInDoubleBlock c) V.field ∈ complexAveragingDomainNearOne c.positivelyOriented}
  field := fun c => complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) V.field) c
section Iterates
variable {K : ℕ}
def partialBlockAverageIter (ω : ℝ) (k : ℕ) (V : PartialGaugeField L m (levelDepth K k)) :
    (i : ℕ) → PartialGaugeField L m (levelDepth K (k + i))
  | 0 => V
  | i + 1 => realPartialBlockAverage ω (partialBlockAverageIter ω k V i)
def complexPartialBlockAverageIter (k : ℕ) (V : PartialGaugeField L m (levelDepth K k)) :
    (i : ℕ) → PartialGaugeField L m (levelDepth K (k + i))
  | 0 => V
  | i + 1 => complexPartialBlockAverage (complexPartialBlockAverageIter k V i)
end Iterates
end PeriodicLattice
end YangMills.Construction
