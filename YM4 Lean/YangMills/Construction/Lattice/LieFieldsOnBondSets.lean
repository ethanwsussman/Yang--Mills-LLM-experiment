import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open Matrices
structure SymmetricBondSet (L m K n : ℕ) where
  bonds : Set (BondAtLevel L m K n)
  opposite_mem : ∀ b ∈ bonds, b.opposite ∈ bonds
variable {L m K n : ℕ}
abbrev PositiveBondsOf (P : SymmetricBondSet L m K n) : Type :=
  {b : BondAtLevel L m K n // b ∈ P.bonds ∧ b.IsPositivelyOriented}
abbrev LieBondField (P : SymmetricBondSet L m K n) : Type :=
  PositiveBondsOf P → ↥ComplexMatrix2.traceless
abbrev LieSiteField (S : Set (SiteAtLevel L m K n)) : Type := ↥S → ↥ComplexMatrix2.traceless
def IsCompactValued {ι : Type*} (f : ι → ↥ComplexMatrix2.traceless) : Prop :=
  ∀ i, (f i : ComplexMatrix2) ∈ ComplexMatrix2.hermitianTraceless
def supOperatorNorm {ι : Type*} (f : ι → ↥ComplexMatrix2.traceless) : ℝ :=
  ⨆ i, ComplexMatrix2.operatorNorm (f i : ComplexMatrix2)
theorem Bond.opposite_isPositivelyOriented {j : ℤ} {b : Bond L m j}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ | hμ⟩ := b.isNeighbour
  · exact absurd ⟨μ, hμ⟩ hb
  · refine ⟨μ, ?_⟩
    change b.source - b.target = _
    rw [← neg_sub, hμ, neg_neg]
namespace LieBondField
variable {P : SymmetricBondSet L m K n}
open Classical in
def eval (a : LieBondField P) (b : BondAtLevel L m K n) : ↥ComplexMatrix2.traceless :=
  if h : b ∈ P.bonds ∧ b.IsPositivelyOriented then a ⟨b, h⟩
  else if h' : b.opposite ∈ P.bonds ∧ b.opposite.IsPositivelyOriented then -a ⟨b.opposite, h'⟩
  else 0
def pathSum (a : LieBondField P) (Γ : List (BondAtLevel L m K n)) : ↥ComplexMatrix2.traceless :=
  (Γ.map a.eval).sum
theorem eval_of_positive (a : LieBondField P) (b : PositiveBondsOf P) : a.eval b.1 = a b := by
  simp only [eval]
  rw [dif_pos b.2]
theorem eval_opposite (a : LieBondField P) (b : PositiveBondsOf P)
    (hb : ¬ b.1.opposite.IsPositivelyOriented) : a.eval b.1.opposite = -a b := by
  have hn : ¬ (b.1.opposite ∈ P.bonds ∧ b.1.opposite.IsPositivelyOriented) := fun x => hb x.2
  have hr : b.1.opposite.opposite = b.1 := rfl
  have hc : b.1.opposite.opposite ∈ P.bonds ∧ b.1.opposite.opposite.IsPositivelyOriented := by
    rw [hr]
    exact b.2
  simp only [eval]
  rw [dif_neg hn, dif_pos hc]
  rfl
end LieBondField
end PeriodicLattice
end YangMills.Construction
