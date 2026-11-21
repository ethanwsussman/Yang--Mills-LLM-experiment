import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def DirichletSiteOperatorsSymmetric : Prop :=
  ∀ S : SequenceDatum, S.toBaseParameters.ZeroFormSymmetries S.region
end YangMills.Construction.SeparatedSequences
end
