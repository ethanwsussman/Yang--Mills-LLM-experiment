import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
open Matrices Conventions
namespace PeriodicLattice
def ConstraintMapDefinedNearZero.Statement : Prop :=
  ∀ (L m K k : ℕ), IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (V : BondAtLevel L m K k → ComplexMatrix2) (Γ : Set (BondAtLevel L m K (k + 1)))
      (c : BondAtLevel L m K (k + 1)), c ∈ Γ → Bond.IsPositivelyOriented c →
      V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) →
      ∀ᶠ B in 𝓝[(supportForms (levelDepth K k) Γ : Set (SupportBond (levelDepth K k) Γ → ComplexMatrix2))] 0,
        ConstraintMapDefined V (extendForm B) c
end PeriodicLattice
end YangMills.Construction
