import YangMills.Construction.Lattice.DirichletOperatorsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open PeriodicLattice PeriodicLattice.DirichletOperators FiniteDimReal RealInnerForms
noncomputable section
namespace SeparatedSequences
namespace AdjointsAndProjections
structure HasDefiningProperties (D : BaseParameters) (Ω : ℕ → Set D.Torus)
    (φ : BondFrame) : Prop where
  zero_adjoint : IsAdjointFor (D.restrictedZeroInner Ω) (D.coarseZeroInner Ω)
    (D.averageZero Ω) (D.averageZeroAdjoint Ω)
  one_adjoint : IsAdjointFor (D.restrictedOneInner Ω φ) (D.coarseOneInner Ω φ)
    (D.averageOne Ω φ) (D.averageOneAdjoint Ω φ)
  gauge_projection : IsOrthogonalProjectionFor (D.restrictedZeroInner Ω)
    (D.laplacianImageOfAverageZeroKernel Ω) (D.gaugeRangeProjection Ω)
  coarse_zero_projection : IsOrthogonalProjectionFor (D.coarseZeroInner (D.withWholeTorus Ω))
    (D.coarseZeroSupported Ω) (D.coarseZeroSupportProjection Ω)
  coarse_one_projection : IsOrthogonalProjectionFor (D.coarseOneInner (D.withWholeTorus Ω) φ)
    (D.coarseOneSupported Ω φ) (D.coarseOneSupportProjection Ω φ)
def Statement : Prop :=
  ∀ (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame),
    HasDefiningProperties D Ω φ
end AdjointsAndProjections
end SeparatedSequences
end
end YangMills.Construction
