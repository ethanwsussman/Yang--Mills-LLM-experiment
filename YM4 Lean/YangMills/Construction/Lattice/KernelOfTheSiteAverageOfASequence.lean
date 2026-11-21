import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SeparatedSequences
open PeriodicLattice.DirichletOperators
def SequenceDatum.AverageKernelPropertiesHold : Prop :=
  ∀ (S : SequenceDatum) (φ : BondFrame),
    S.toBaseParameters.AverageKernelProperties S.region φ
end YangMills.Construction.SeparatedSequences
