import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def MassiveOperatorsRelatedByDifferential : Prop :=
  ∀ (S : SequenceDatum) (φ : BondFrame),
    S.toBaseParameters.MassiveOperatorsRelation S.region φ
end YangMills.Construction.SeparatedSequences
end
