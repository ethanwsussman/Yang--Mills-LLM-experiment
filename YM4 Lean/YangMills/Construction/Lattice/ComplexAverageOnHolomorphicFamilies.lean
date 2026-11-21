import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.HolomorphicFieldFamilies
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def HolomorphicFamilyComplexAverage : Prop :=
  ∀ (L m K k : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
      (W : Set (ι ⊕ κ → Matrices.ComplexMatrix2))
      (U : (ι ⊕ κ → Matrices.ComplexMatrix2) → BondAtLevel L m K k → Matrices.ComplexMatrix2),
      IsHolomorphicGaugeFieldFamily b W U →
      ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
        Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct ι κ)
          {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
            Set (BondAtLevel L m K k → Matrices.ComplexMatrix2))} ∧
        MapsTo (fun p => complexBlockAverage (U p) c)
          {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
            Set (BondAtLevel L m K k → Matrices.ComplexMatrix2))}
          complexGaugeGroup ∧
        Matrices.GroupLieProduct.IsHolomorphicToMatrixEntries b
          {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
            Set (BondAtLevel L m K k → Matrices.ComplexMatrix2))}
          (fun p => complexBlockAverage (U p) c) ∧
        ∀ B : (ι ⊕ κ → Matrices.ComplexMatrix2) → BondAtLevel L m K k → Matrices.ComplexMatrix2,
          IsHolomorphicBondFormFamily b W B →
          Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct ι κ)
            {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
              Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) ∧
              ConstraintMapDefined (U p) (B p) c} ∧
          Matrices.GroupLieProduct.IsHolomorphicToTraceless b
            {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
              Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) ∧
              ConstraintMapDefined (U p) (B p) c}
            (fun p => constraintMap (U p) (B p) c)
end YangMills.Construction.PeriodicLattice
