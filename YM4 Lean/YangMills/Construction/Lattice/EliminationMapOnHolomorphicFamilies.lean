import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.HolomorphicFieldFamilies
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def EliminationPreservesHolomorphicForms : Prop :=
  ∀ (L m K k : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (e : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
      (Ω : Set (ι ⊕ κ → Matrices.ComplexMatrix2))
      (U : (ι ⊕ κ → Matrices.ComplexMatrix2) → BondAtLevel L m K k → Matrices.ComplexMatrix2),
      IsHolomorphicGaugeFieldFamily e Ω U →
      ∀ Γ : Set (BondAtLevel L m K (k + 1)), (∀ c ∈ Γ, c.IsPositivelyOriented) →
        (∀ z ∈ Ω, ComplexConstraintDefined (U z) Γ) →
        (∀ z ∈ Ω, ∀ c ∈ Γ, PivotCoeffInvertible (U z) c) →
        ∀ A : (ι ⊕ κ → Matrices.ComplexMatrix2) → BondAtLevel L m K k → Matrices.ComplexMatrix2,
          IsHolomorphicBondFormFamily e Ω A →
          IsHolomorphicBondFormFamily e Ω fun z => eliminate (U z) Γ (A z)
end YangMills.Construction.PeriodicLattice
end
