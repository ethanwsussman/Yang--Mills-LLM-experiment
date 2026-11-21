import YangMills.Construction.Lattice.BondwiseAveragesUnderReversal
import YangMills.Construction.Lattice.PositiveOneOfABondAndItsReverse
import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
namespace ReversalAverages
variable {L m : ℕ} {j j' : ℤ}
theorem det_pathHolonomy {V : Bond L m j' → ComplexMatrix2} (hV : ∀ b, (V b).det = 1)
    (γ : List (Bond L m j')) : (pathHolonomy V γ).det = 1 := by apply _root_.YangMills.SharedProofs.p29622 <;> assumption
theorem isUnit_parallelTransport {V : Bond L m j' → ComplexMatrix2} (hV : ∀ b, (V b).det = 1)
    (c : Bond L m j) : IsUnit (parallelTransport V c) := by
  rw [Matrix.isUnit_iff_isUnit_det, parallelTransport, det_pathHolonomy hV]
  exact isUnit_one
theorem isUnit_matExp_mul_parallelTransport {V : Bond L m j' → ComplexMatrix2}
    (hV : ∀ b, (V b).det = 1) (c : Bond L m j) (Z : ComplexMatrix2) :
    IsUnit (ComplexMatrix2.matExp Z * parallelTransport V c) :=
  (Matrix.isUnit_exp Z).mul (isUnit_parallelTransport hV c)
theorem isUnit_blockAverageOnPositive (ω : ℝ) {V : Bond L m j' → ComplexMatrix2}
    (hV : ∀ b, (V b).det = 1) (c : Bond L m j) : IsUnit (blockAverageOnPositive ω V c) := by
  unfold blockAverageOnPositive regularAverageValue logAverageValue
  split_ifs
  · exact isUnit_matExp_mul_parallelTransport hV c _
  · exact isUnit_matExp_mul_parallelTransport hV c _
  · exact isUnit_parallelTransport hV c
theorem isUnit_complexBlockAverageOnPositive {V : Bond L m j' → ComplexMatrix2}
    (hV : ∀ b, (V b).det = 1) (c : Bond L m j) : IsUnit (complexBlockAverageOnPositive V c) :=
  isUnit_matExp_mul_parallelTransport hV c _
theorem mul_opposite_eq_one (A : Bond L m j → ComplexMatrix2) (c : Bond L m j)
    (hx : Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented) (hA : IsUnit (A c))
    (hA' : IsUnit (A c.opposite)) :
    (open Classical in
      if c.IsPositivelyOriented then A c else (A c.opposite)⁻¹) *
      (open Classical in
        if c.opposite.IsPositivelyOriented then A c.opposite else (A c.opposite.opposite)⁻¹)
      = 1 := by
  have hoo : c.opposite.opposite = c := rfl
  rcases hx with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [if_pos h, if_neg h', hoo]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA)
  · rw [if_neg h', if_pos h]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hA')
theorem det_extendByOne {S ℬ : Set (Bond L m j')} {V : Bond L m j' → ComplexMatrix2}
    (hS : S ⊆ ℬ) (hV : ∀ b ∈ ℬ, (V b).det = 1) (b : Bond L m j') :
    (onSetElseOne S V b).det = 1 := by
  unfold onSetElseOne
  split_ifs with h
  · exact hV b (hS h)
  · exact Matrix.det_one
end ReversalAverages
open ReversalAverages in
theorem partialBlockAverageReversalInverse_of_orientation
    (hPos : PositiveOrientationOfBondAndOpposite) : PartialBlockAverageReversalInverse := by
  intro L m K hL hm hK j hj ℬ _
  have hc := hPos L m K hL hm hK j hj
  have hsame : ∀ c : BondAtLevel L m K (j + 1),
      c.opposite.positivelyOriented = c.positivelyOriented := fun c => (hc c).2.2.2.2.2.1
  have hbonds : ∀ c : BondAtLevel L m K (j + 1),
      (bondsInDoubleBlock c.opposite : Set (BondAtLevel L m K j)) = bondsInDoubleBlock c := by
    intro c
    rw [← (hc c.opposite).2.2.2.2.2.2, hsame c, (hc c).2.2.2.2.2.2]
  have hxor : ∀ c : BondAtLevel L m K (j + 1),
      Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented :=
    fun c => (hc c).2.1
  refine ⟨fun V hV => ⟨?_, ?_⟩, fun V hV => ⟨?_, ?_⟩⟩
  · intro c hcb
    change (bondsInDoubleBlock c.opposite : Set (BondAtLevel L m K j)) ⊆ ℬ
    rw [hbonds c]
    exact hcb
  · intro c hcb
    have hdet : ∀ b ∈ ℬ, (V b).det = 1 := fun b hb =>
      (Matrix.mem_specialUnitaryGroup_iff.1 (hV.1 b hb)).2
    have hext := det_extendByOne
      (hcb : (bondsInDoubleBlock c : Set (BondAtLevel L m K j)) ⊆ ℬ) hdet
    change blockAverage (Averaging.smoothingRadius L) (onSetElseOne (bondsInDoubleBlock c) V) c *
      blockAverage (Averaging.smoothingRadius L)
        (onSetElseOne (bondsInDoubleBlock c.opposite) V) c.opposite = 1
    rw [hbonds c]
    exact mul_opposite_eq_one _ c (hxor c) (isUnit_blockAverageOnPositive _ hext c)
      (isUnit_blockAverageOnPositive _ hext c.opposite)
  · rintro c ⟨hcb, hdom⟩
    refine ⟨?_, ?_⟩
    · change (bondsInDoubleBlock c.opposite : Set (BondAtLevel L m K j)) ⊆ ℬ
      rw [hbonds c]
      exact hcb
    · change onSetElseOne (bondsInDoubleBlock c.opposite) V ∈
        complexAveragingDomainNearOne c.opposite.positivelyOriented
      rw [hbonds c, hsame c]
      exact hdom
  · rintro c ⟨hcb, -⟩
    have hdet : ∀ b ∈ ℬ, (V b).det = 1 := fun b hb => hV.1 b hb
    have hext := det_extendByOne
      (hcb : (bondsInDoubleBlock c : Set (BondAtLevel L m K j)) ⊆ ℬ) hdet
    change complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) V) c *
      complexBlockAverage (onSetElseOne (bondsInDoubleBlock c.opposite) V) c.opposite = 1
    rw [hbonds c]
    exact mul_opposite_eq_one _ c (hxor c) (isUnit_complexBlockAverageOnPositive hext c)
      (isUnit_complexBlockAverageOnPositive hext c.opposite)
end YangMills.Construction.PeriodicLattice
