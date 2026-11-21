import YangMills.Construction.Lattice.IteratesOfAComplexConfiguration
import YangMills.Construction.Lattice.MinimalConfigurationsAtComplexData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ComplexAverageEqComplexIterate : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    ∀ (B : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
      (j : ℕ), j ≤ K →
      ∀ c : BondAtLevel L m K j,
        (ComplexAverageIsDefined K B U j c ↔ ComplexIterateDefinedAt B U j c) ∧
        (ComplexIterateDefinedAt B U j c →
          complexBlockFieldAtLevel j U c = complexIterate B U j c)
end YangMills.Construction.PeriodicLattice
