import YangMills.Construction.Lattice.OneStepCovarianceAndDomains
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def pivotScale (L : ℕ) : ℝ := 1 / 48 * stepRadius L
def pivotInnerScale (L : ℕ) : ℝ := pivotScale L ^ 2 / (2 * (L : ℝ) ^ 3)
variable {L m K n : ℕ}
def setWithoutPivot (c : BondAtLevel L m K (n + 1)) : SymmetricBondSet L m K n where
  bonds := (doubleBlockSymmetricSet c).bonds \
    {(pivot c : BondAtLevel L m K n), (pivot c : BondAtLevel L m K n).opposite}
  opposite_mem := by
    rintro e ⟨he, hnot⟩
    refine ⟨(doubleBlockSymmetricSet c).opposite_mem e he, fun hmem => hnot ?_⟩
    rcases hmem with hmem | hmem
    · exact Or.inr (congrArg Bond.opposite hmem)
    · exact Or.inl (congrArg Bond.opposite hmem)
def extendAtPivot (c : BondAtLevel L m K (n + 1)) (a' : LieBondField (setWithoutPivot c))
    (x : ↥Matrices.ComplexMatrix2.traceless) : LieBondField (doubleBlockSymmetricSet c) :=
  open Classical in
  fun b => if b.1 = (pivot c : BondAtLevel L m K n) then x else a'.eval b.1
end YangMills.Construction.PeriodicLattice
