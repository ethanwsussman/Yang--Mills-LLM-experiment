import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.EndPointsAndOrientationOfABond
import YangMills.Construction.Lattice.PositiveOneOfABondAndItsReverse
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
theorem positiveOrientationOfBondAndOpposite_holds
    (hEnds : BondEndpointsOrientation.Statement)
    (hDouble : DoubleBlockStructure.Statement) :
    PositiveOrientationOfBondAndOpposite := by
  intro L m K hL hm hK j hj c
  obtain ⟨⟨-, -, -, hside⟩, -, -, hBonds⟩ :=
    hEnds ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ (j + 1) hj
  obtain ⟨-, -, hne, hoo, -, hxor⟩ := hBonds c
  have hside' : 2 < sideInLevelUnits L m K (j + 1) := hside
  have hne' : c.opposite ≠ c := hne
  have hoo' : c.opposite.opposite = c := hoo
  have hxor' : Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented := hxor
  obtain ⟨⟨-, -, -, hopp, -⟩, -⟩ := hDouble L m K j hL hm hj c
  rcases hxor' with ⟨hp, hnq⟩ | ⟨hq, hnp⟩
  · have e₁ : c.positivelyOriented = c := if_pos hp
    have e₂ : c.opposite.positivelyOriented = c := (if_neg hnq).trans hoo'
    rw [e₂, e₁]
    exact ⟨hside', Or.inl ⟨hp, hnq⟩, hp, Or.inl rfl, Or.inl ⟨rfl, fun h => hne' h.symm⟩, rfl, rfl⟩
  · have e₁ : c.positivelyOriented = c.opposite := if_neg hnp
    have e₂ : c.opposite.positivelyOriented = c.opposite := if_pos hq
    rw [e₂, e₁, hoo']
    exact ⟨hside', Or.inr ⟨hq, hnp⟩, hq, Or.inr rfl, Or.inr ⟨rfl, fun h => hne' h.symm⟩, rfl, hopp⟩
end YangMills.Construction.PeriodicLattice
