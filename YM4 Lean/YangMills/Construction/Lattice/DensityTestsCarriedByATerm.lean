import YangMills.Construction.Lattice.ClassesAndDropOuts
import YangMills.Construction.Lattice.SmallFieldDomainOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set ParameterChoice Matrices
namespace PeriodicLattice.CubesOfStep
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ)
def untouchedDensityCubes (k : ℕ) (R : Set (FourTorus c.L m)) (E : Set (Set (FourTorus c.L m))) :
    Set (Set (FourTorus c.L m)) :=
  partitionCubesIn (densityPartitionIndex c K x k) R \
    ⋃ X ∈ E, partitionCubesIn (densityPartitionIndex c K x k)
      (shrunkenCore c K x (Nat.log c.L c.M) k X)
def densityWeight {k : ℕ} (S : LabelAtLevel c m K x k) {D : Type}
    {W : Set (Set (FourTorus c.L m))} (O : LargeFieldOutcome D W)
    (V : BondAtLevel c.L m K k → ComplexMatrix2) : ℝ :=
  (∏ᶠ Q ∈ untouchedDensityCubes c K x k (S.domainSeq k) O.classTwo,
      densityCubeIndicator c K x k V Q) *
    ∏ᶠ X ∈ O.classTwo, secondKindIndicator c K x (Nat.log c.L c.M) k V X
end PeriodicLattice.CubesOfStep
end YangMills.Construction
