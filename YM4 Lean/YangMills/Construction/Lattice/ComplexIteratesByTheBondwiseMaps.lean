import YangMills.Construction.Lattice.BondwiseAverage
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def bareComplexPartialIter (V : PartialGaugeField L m (levelDepth K 0)) (i : ℕ) :
    PartialGaugeField L m (levelDepth K i) :=
  cast (by rw [Nat.zero_add]) (complexPartialBlockAverageIter 0 V i)
def complexPartialValues (k : ℕ) (V : PartialGaugeField L m (levelDepth K k)) :
    (i : ℕ) → Bond L m (levelDepth K (k + i)) → Matrices.ComplexMatrix2
  | 0 => V.field
  | i + 1 => fun c => complexBlockAverage
      (onSetElseOne (bondsInDoubleBlock c) (complexPartialValues k V i)) c
def ComplexPartialDefinedAt (k : ℕ) (V : PartialGaugeField L m (levelDepth K k)) :
    (i : ℕ) → Bond L m (levelDepth K (k + i)) → Prop
  | 0, b => b ∈ V.support
  | i + 1, c => (∀ b ∈ (bondsInDoubleBlock c : Set (Bond L m (levelDepth K (k + i)))),
        ComplexPartialDefinedAt k V i b) ∧
      onSetElseOne (bondsInDoubleBlock c) (complexPartialValues k V i) ∈
        complexAveragingDomainNearOne c.positivelyOriented
end YangMills.Construction.PeriodicLattice
