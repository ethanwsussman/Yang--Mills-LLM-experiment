import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
def IsNearOneOnDoubleBlock (ε : ℝ) (c : BondAtLevel L m K (n + 1))
    (W : BondAtLevel L m K n → Matrices.ComplexMatrix2) : Prop :=
  IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W ∧
    ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
      Matrices.ComplexMatrix2.operatorNorm (W b - 1) ≤ ε
structure SchemeObjectsNearOne (η : ℝ) (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (W : BondAtLevel L m K n → Matrices.ComplexMatrix2) : Prop where
  isDefined : IsSchemeAverageDefined s W c
  contourNear : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      Matrices.ComplexMatrix2.operatorNorm (contourHolonomy s W y x - 1) ≤ η
  averageNear : Matrices.ComplexMatrix2.operatorNorm (schemeBlockAverage s W c - 1) ≤ η
  axialNear : ∀ x ∈ sitesInBlock (levelDepth K n) c.source, ∀ b ∈ crossingPath c x,
    Matrices.ComplexMatrix2.operatorNorm (pathHolonomy W (axialPath x b.source) - 1) ≤ η
def SchemeObjectsNearOneUniformly : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧
    ∀ m K n : ℕ, 0 < m → n < K →
      ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented →
      ∀ W : BondAtLevel L m K n → Matrices.ComplexMatrix2, IsNearOneOnDoubleBlock ε c W →
        SchemeObjectsNearOne η s c W
end YangMills.Construction.PeriodicLattice
end
