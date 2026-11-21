import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction.PeriodicLattice.DirichletLaplacianSplitsOffBoundary
def Statement : Prop :=
  ∀ (S : SeparatedSequences.SequenceDatum) (φ : BondFrame),
    S.toBaseParameters.DirichletLaplacianSplitting S.region φ
end YangMills.Construction.PeriodicLattice.DirichletLaplacianSplitsOffBoundary
