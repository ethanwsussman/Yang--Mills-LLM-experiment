import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def LinearAverageIsometryCovariance : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ j j' : ℤ, 0 ≤ j → j' = j + 1 →
    (∀ A : Bond L m j' → Matrices.ComplexMatrix2, IsBondForm complexLieAlgebra A →
      IsBondForm complexLieAlgebra (linearBlockAverage A : Bond L m j → Matrices.ComplexMatrix2) ∧
      IsBondForm complexLieAlgebra
        (scaledLinearBlockAverage A : Bond L m j → Matrices.ComplexMatrix2)) ∧
    ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ j → ∀ σ ∈ latticeIsometries L m i,
    ∀ (A : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j),
      linearBlockSum (transportForm σ A) (bondImage σ c) = linearBlockSum A c
end PeriodicLattice
end YangMills.Construction
