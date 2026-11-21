import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
open PeriodicLattice.DirichletOperators
def SequenceConditionsGaugeInvariant : Prop :=
  ∀ (S : SequenceDatum) (φ : BondFrame),
    S.toBaseParameters.GaugeFixingProperties S.region φ
end SeparatedSequences
end YangMills.Construction
end
