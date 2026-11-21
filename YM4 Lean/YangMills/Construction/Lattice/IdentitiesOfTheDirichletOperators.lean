import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
def DirichletOperatorIdentities : Prop :=
  ∀ (S : SequenceDatum) (φ : PeriodicLattice.DirichletOperators.BondFrame),
    let D := S.toBaseParameters
    let Ω := S.region
    D.GradCurlIdentities Ω φ ∧ D.DirichletLaplacianSplitting Ω φ ∧
      D.HodgeLaplacianSplitting Ω φ ∧ D.GradLaplacianCommutation Ω φ ∧
      D.MulCommutators Ω φ ∧ D.ZeroFormSymmetries Ω ∧ D.AverageKernelProperties Ω φ ∧
      D.GaugeProjectionFormulas Ω ∧ D.ConstrainedGreenProperties Ω ∧
      D.VariationalAndGaussianForms Ω ∧
      D.ZeroFormMinimizer Ω ∧ D.ConsecutiveLevelWeights ∧ D.AverageGradIntertwining Ω φ ∧
      D.GaugeFixingProperties Ω φ ∧ D.MassiveOneOperatorForms Ω φ ∧
      D.MassiveOperatorsRelation Ω φ ∧ D.OneGreenProducts Ω φ ∧ D.OneExtensionProperties Ω φ ∧
      D.OneFormProjections Ω φ ∧ D.OneGreenDecomposition Ω φ
end SeparatedSequences
end YangMills.Construction
end
