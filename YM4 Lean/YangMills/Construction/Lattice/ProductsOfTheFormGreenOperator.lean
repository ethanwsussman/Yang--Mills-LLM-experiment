import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
namespace GreenOperatorProducts
def Statement : Prop :=
  ∀ (S : SequenceDatum) (φ : BondFrame),
    S.toBaseParameters.OneGreenProducts S.region φ
end GreenOperatorProducts
end SeparatedSequences
end YangMills.Construction
end
