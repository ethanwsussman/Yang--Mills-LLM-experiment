import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def LinearizingCorrectionExistsAndIsLocallyUnique : Prop :=
  ∀ (L m K k : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
      (Γ : Set (BondAtLevel L m K (k + 1))),
      (∀ c ∈ Γ, c.IsPositivelyOriented) → ComplexConstraintDefined V Γ →
      (∀ c ∈ Γ, PivotCoeffInvertible V c) →
      (∃ N D, IsLinearizingCorrection V Γ N D) ∧
      ∀ N₁ D₁ N₂ D₂, IsLinearizingCorrection V Γ N₁ D₁ → IsLinearizingCorrection V Γ N₂ D₂ →
        ∀ᶠ B in 𝓝[(supportForms (levelDepth K k) Γ :
            Set (SupportBond (levelDepth K k) Γ → Matrices.ComplexMatrix2))] 0,
          D₁ B = D₂ B
end YangMills.Construction.PeriodicLattice
