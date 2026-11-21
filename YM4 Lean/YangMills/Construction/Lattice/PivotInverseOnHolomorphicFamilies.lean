import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.HolomorphicFieldFamilies
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def PivotInverseHolomorphic : Prop :=
  ∀ (L m K k : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
      (W : Set (ι ⊕ κ → Matrices.ComplexMatrix2))
      (U : (ι ⊕ κ → Matrices.ComplexMatrix2) → BondAtLevel L m K k → Matrices.ComplexMatrix2),
      IsHolomorphicGaugeFieldFamily b W U →
      ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
        (∀ p ∈ W, U p ∈
          (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2))) →
        Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct ι κ)
          {p | p ∈ W ∧ PivotCoeffInvertible (U p) c} ∧
        ∀ ν : (ι ⊕ κ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2,
          Matrices.GroupLieProduct.IsHolomorphicToTraceless b
            {p | p ∈ W ∧ PivotCoeffInvertible (U p) c} ν →
          Matrices.GroupLieProduct.IsHolomorphicToTraceless b
            {p | p ∈ W ∧ PivotCoeffInvertible (U p) c}
            fun p => pivotCoeffInv (U p) c (ν p)
end YangMills.Construction.PeriodicLattice
