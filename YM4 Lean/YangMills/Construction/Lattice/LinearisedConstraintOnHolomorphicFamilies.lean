import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.HolomorphicFieldFamilies
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def HolomorphicConstraint.claim : Prop :=
  ∀ (L m K k : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
      (W : Set (ι ⊕ κ → Matrices.ComplexMatrix2))
      (U : (ι ⊕ κ → Matrices.ComplexMatrix2) → BondAtLevel L m K k → Matrices.ComplexMatrix2),
      IsHolomorphicGaugeFieldFamily b W U →
      ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
        (∀ p ∈ W, U p ∈
          (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2))) →
        (∀ A : (ι ⊕ κ → Matrices.ComplexMatrix2) → BondAtLevel L m K k → Matrices.ComplexMatrix2,
          IsHolomorphicBondFormFamily b W A →
          Matrices.GroupLieProduct.IsHolomorphicToTraceless b W
            fun p => linearizedConstraint (U p) (A p) c) ∧
        ∀ A₁ A₂ : (ι ⊕ κ → Matrices.ComplexMatrix2) → BondAtLevel L m K k →
            Matrices.ComplexMatrix2,
          IsHolomorphicBondFormFamily b W A₁ →
          IsHolomorphicBondFormFamily b W A₂ →
          Matrices.GroupLieProduct.IsHolomorphicToTraceless b W
            fun p => constraintBilinear (U p) (A₁ p) (A₂ p) c
end YangMills.Construction.PeriodicLattice
end
