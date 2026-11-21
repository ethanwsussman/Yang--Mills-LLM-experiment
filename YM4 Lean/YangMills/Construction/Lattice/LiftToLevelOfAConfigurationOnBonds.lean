import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.BondwiseAverage
import YangMills.Construction.Lattice.LiftOfOrder
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K k : ℕ}
def IsLevelLiftData (𝒢 : Set Matrices.ComplexMatrix2) (j : ℕ)
    (V : PartialGaugeField L m (levelDepth K k)) : Prop :=
  j ≤ k ∧ k ≤ K ∧ IsReversalClosed V.support ∧ IsGaugeField 𝒢 V.support V.field
def bareLiftSupport : {k : ℕ} → Set (BondAtLevel L m K k) → Set (BondAtLevel L m K 0)
  | 0, S => S
  | _ + 1, S => liftSupport 0 S
def bareLiftPartial (V : PartialGaugeField L m (levelDepth K k)) :
    PartialGaugeField L m (levelDepth K 0) where
  support := bareLiftSupport (K := K) V.support
  field := bareLiftFromLevel (K := K) V.field
def levelLiftPartial (j : ℕ) (V : PartialGaugeField L m (levelDepth K k)) :
    PartialGaugeField L m (levelDepth K j) :=
  cast (by rw [Nat.zero_add])
    (partialBlockAverageIter (K := K) (Averaging.smoothingRadius L) 0 (bareLiftPartial V) j)
def complexLevelLiftPartial (j : ℕ) (V : PartialGaugeField L m (levelDepth K k)) :
    PartialGaugeField L m (levelDepth K j) :=
  cast (by rw [Nat.zero_add]) (complexPartialBlockAverageIter (K := K) 0 (bareLiftPartial V) j)
end PeriodicLattice
end YangMills.Construction
