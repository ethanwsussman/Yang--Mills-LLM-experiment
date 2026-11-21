import YangMills.Construction.Lattice.DirichletOperatorsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SiteOperatorPositivity
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.FiniteDimReal
variable (D : SeparatedSequences.BaseParameters) (Ω : ℕ → Set D.Torus)
structure SiteOperatorsPositive : Prop where
  massivePosDef : IsPosDefFor (D.restrictedZeroInner Ω) (D.massiveZeroOperator Ω)
  massiveIsUnit : IsUnit (D.massiveZeroOperator Ω)
  greenPosDef : IsPosDefFor (D.restrictedZeroInner Ω) (D.zeroGreen Ω)
  laplacianInjOn :
    InjOn (dirichletLaplacian D.K D.t (Ω 0))
      (D.averageZeroKernel Ω : Set ↥(zeroFormsOn D.K (Ω 0)))
  averagedGreenSqPosDef :
    IsPosDefFor (D.coarseZeroInner Ω) (D.averagedZeroGreenSq Ω)
  averagedGreenPosDef : IsPosDefFor (D.coarseZeroInner Ω)
    (D.averageZero Ω ∘ₗ D.zeroGreen Ω ∘ₗ D.averageZeroAdjoint Ω)
  averagedGreenSqIsUnit : IsUnit (D.averagedZeroGreenSq Ω)
def AllSiteOperatorsPositive : Prop :=
  ∀ D : SeparatedSequences.SequenceDatum, SiteOperatorsPositive D.toBaseParameters D.region
end YangMills.Construction.SiteOperatorPositivity
end
