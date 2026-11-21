import YangMills.Construction.Averaging.SingleStepConstants
import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.OneStepSchemes
import YangMills.Construction.Matrices.SpecialUnitaryAngles
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
variable {L m K n : ℕ}
structure SingleStepBoundsAt (s : AveragingScheme) (W : BondAtLevel L m K n → ComplexMatrix2)
    (c : BondAtLevel L m K (n + 1)) : Prop where
  defined : IsSchemeAverageDefined s W c
  contourHolonomy_mem : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y, contourHolonomy s W y x ∈ compactGaugeGroup
  average_mem : schemeBlockAverage s W c ∈ compactGaugeGroup
  rotationAngle_le : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y, ∀ Γ ∈ contourSet y x,
      ComplexMatrix2.rotationAngle (pathHolonomy W Γ * (contourHolonomy .centred W y x)⁻¹) ≤
        Averaging.SingleStep.loopAngleConstant L * doubleBlockCurvature W c
  localDefect_le : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
    ComplexMatrix2.operatorNorm (localDefect s W c x - 1) ≤
      Averaging.SingleStep.loopVariableConstant L * doubleBlockCurvature W c
  average_eq : ∃ Y ∈ ComplexMatrix2.hermitianTraceless,
    ComplexMatrix2.operatorNorm Y ≤
        Averaging.SingleStep.meanLogConstant L * doubleBlockCurvature W c ∧
      schemeBlockAverage s W c = ComplexMatrix2.matExp (Complex.I • Y) * baseTransport s W c
def SingleStepBounds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented →
      ∀ (s : AveragingScheme) (W : BondAtLevel L m K n → ComplexMatrix2),
        IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W →
        doubleBlockCurvature W c <
          min (Averaging.smoothingRadius L) (Averaging.SingleStep.loopVariableConstant L)⁻¹ →
        SingleStepBoundsAt s W c
end PeriodicLattice
end YangMills.Construction
