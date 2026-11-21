import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice.DirichletOperators
namespace GaugeProjections
def RepresentationStatement : Prop :=
  ∀ S : SeparatedSequences.SequenceDatum, S.GaugeProjectionFormulas S.region
end GaugeProjections
end YangMills.Construction
end
