import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondwiseAverage
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices Conventions
namespace PeriodicLattice
variable {L m K : ℕ}
def IsComplexIterationData (j : ℕ) (S : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  IsAdmissibleBlockingFactor L ∧ 0 < m ∧ 0 < K ∧ j ≤ K ∧ IsReversalClosed S ∧
    IsGaugeField complexGaugeGroup S U
def complexIteratePartial (S : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (i : ℕ) → PartialGaugeField L m (levelDepth K i)
  | 0 => ⟨S, U⟩
  | i + 1 => complexPartialBlockAverage (complexIteratePartial S U i)
def ComplexIterateDefinedAt (S : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (i : ℕ) (c : BondAtLevel L m K i) : Prop :=
  c ∈ (complexIteratePartial S U i).support
def complexIterate (S : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → ComplexMatrix2) (i : ℕ) :
    BondAtLevel L m K i → ComplexMatrix2 :=
  (complexIteratePartial S U i).field
theorem bondsInDoubleBlock_opposite {j j' : ℤ} (c : Bond L m j) :
    (bondsInDoubleBlock c.opposite : Set (Bond L m j')) = bondsInDoubleBlock c := by
  simp only [bondsInDoubleBlock, bondDoubleBlock, Bond.opposite, union_comm]
theorem positivelyOriented_eq_self {j : ℤ} {c : Bond L m j} (hc : c.IsPositivelyOriented) :
    c.positivelyOriented = c :=
  if_pos hc
theorem positivelyOriented_opposite {j : ℤ} {c : Bond L m j}
    (hc : ¬c.opposite.IsPositivelyOriented) : c.opposite.positivelyOriented = c := by
  rw [Bond.positivelyOriented, if_neg hc]
  exact Bond.ext rfl rfl
theorem complexIterateDefinedAt_succ (S : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) (i : ℕ) {c : BondAtLevel L m K (i + 1)}
    (hc : c.IsPositivelyOriented) :
    ComplexIterateDefinedAt S U (i + 1) c ↔
      (∀ e ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K i)), ComplexIterateDefinedAt S U i e) ∧
        onSetElseOne (bondsInDoubleBlock c) (complexIterate S U i) ∈
          complexAveragingDomainNearOne c := by
  change (bondsInDoubleBlock c ⊆ (complexIteratePartial S U i).support ∧
    onSetElseOne (bondsInDoubleBlock c) (complexIteratePartial S U i).field ∈
      complexAveragingDomainNearOne c.positivelyOriented) ↔ _
  rw [positivelyOriented_eq_self hc]
  rfl
theorem complexIterateDefinedAt_succ_opposite (S : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) (i : ℕ) {c : BondAtLevel L m K (i + 1)}
    (hc : c.IsPositivelyOriented) (hc' : ¬c.opposite.IsPositivelyOriented) :
    ComplexIterateDefinedAt S U (i + 1) c.opposite ↔ ComplexIterateDefinedAt S U (i + 1) c := by
  rw [complexIterateDefinedAt_succ S U i hc]
  change (bondsInDoubleBlock c.opposite ⊆ (complexIteratePartial S U i).support ∧
    onSetElseOne (bondsInDoubleBlock c.opposite) (complexIteratePartial S U i).field ∈
      complexAveragingDomainNearOne c.opposite.positivelyOriented) ↔ _
  rw [positivelyOriented_opposite hc', bondsInDoubleBlock_opposite]
  rfl
theorem complexIterate_succ (S : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) (i : ℕ) {c : BondAtLevel L m K (i + 1)}
    (hc : c.IsPositivelyOriented) :
    complexIterate S U (i + 1) c =
      complexBlockAverageOnPositive
        (onSetElseOne (bondsInDoubleBlock c) (complexIterate S U i)) c := by
  change complexBlockAverage
    (onSetElseOne (bondsInDoubleBlock c) (complexIteratePartial S U i).field) c = _
  rw [complexBlockAverage, if_pos hc]
  rfl
theorem complexIterate_succ_opposite (S : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) (i : ℕ) {c : BondAtLevel L m K (i + 1)}
    (hc : c.IsPositivelyOriented) (hc' : ¬c.opposite.IsPositivelyOriented) :
    complexIterate S U (i + 1) c.opposite = (complexIterate S U (i + 1) c)⁻¹ := by
  rw [complexIterate_succ S U i hc]
  change complexBlockAverage
    (onSetElseOne (bondsInDoubleBlock c.opposite) (complexIteratePartial S U i).field)
      c.opposite = _
  rw [complexBlockAverage, if_neg hc', bondsInDoubleBlock_opposite]
  have hoo : c.opposite.opposite = c := Bond.ext rfl rfl
  rw [hoo]
  rfl
end PeriodicLattice
end YangMills.Construction
