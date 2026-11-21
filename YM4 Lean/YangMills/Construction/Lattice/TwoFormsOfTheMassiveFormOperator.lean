import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
def MassiveOneOperatorHasTwoForms : Prop :=
  ∀ (S : SequenceDatum) (φ : BondFrame),
    S.toBaseParameters.MassiveOneOperatorForms S.region φ
end SeparatedSequences
end YangMills.Construction
end
