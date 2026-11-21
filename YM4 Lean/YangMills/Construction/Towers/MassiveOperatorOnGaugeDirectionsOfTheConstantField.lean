import YangMills.Construction.Towers.TheCoefficientAsAResponseToAConstantField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
def GaugeDirectionHessianIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (f : ℝ) (l : FullSpace.Vertex L 0 0 → Matrices.ComplexMatrix2),
    (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) → HasFiniteSupp l →
    FullSpace.abelianMassiveHessian (AbelianFieldDensity.scaledLinearAngle L f)
        (FullSpace.covDiff
          (FullSpace.abelianLinkField (AbelianFieldDensity.scaledLinearAngle L f)) l) =
      FullSpace.covDiff
        (FullSpace.abelianLinkField (AbelianFieldDensity.scaledLinearAngle L f))
        (FullSpace.covDiffAdjoint
          (FullSpace.abelianLinkField (AbelianFieldDensity.scaledLinearAngle L f))
          (FullSpace.covDiff
            (FullSpace.abelianLinkField (AbelianFieldDensity.scaledLinearAngle L f)) l))
end YangMills.Construction.Tower.ConstantFieldSymbols
end
