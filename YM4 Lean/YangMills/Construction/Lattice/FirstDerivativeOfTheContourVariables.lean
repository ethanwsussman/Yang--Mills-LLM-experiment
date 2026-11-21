import YangMills.Construction.Lattice.OneStepCovarianceAndDomains
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ContourHolonomyDerivative.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented →
    ∀ a : LieBondField (doubleBlockSymmetricSet c),
    ∀ y ∈ bondEndpoints c, ∀ x ∈ sitesInBlock (levelDepth K n) y,
      HasDerivAt (fun t : ℂ => contourHolonomy s (expBondField c (t • a)) y x)
        (Complex.I • contourFormMean s (fun b => (a.eval b : Matrices.ComplexMatrix2)) y x) 0
end YangMills.Construction.PeriodicLattice
