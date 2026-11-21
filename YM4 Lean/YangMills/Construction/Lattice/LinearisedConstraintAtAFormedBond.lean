import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
variable {L m : ℕ}
structure LinearizedConstraintProperties {K k : ℕ} (V : BondAtLevel L m K k → ComplexMatrix2)
    (c : BondAtLevel L m K (k + 1)) : Prop where
  differentiableAt_logRatioCurve : ∀ A : BondAtLevel L m K k → ComplexMatrix2,
    IsBondForm complexLieAlgebra A →
    DifferentiableAt ℝ (logRatioCurve complexBlockAverage V A c) 0
  map_add : ∀ A A' : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
    IsBondForm complexLieAlgebra A' →
      linearizedConstraint V (A + A') c = linearizedConstraint V A c + linearizedConstraint V A' c
  map_smul : ∀ (z : ℂ) (A : BondAtLevel L m K k → ComplexMatrix2),
    IsBondForm complexLieAlgebra A →
    linearizedConstraint V (z • A) c = z • linearizedConstraint V A c
  mem_complexLieAlgebra : ∀ A : BondAtLevel L m K k → ComplexMatrix2,
    IsBondForm complexLieAlgebra A →
    linearizedConstraint V A c ∈ complexLieAlgebra
  eq_of_eqOn_doubleBlock : ∀ A A' : BondAtLevel L m K k → ComplexMatrix2,
    IsBondForm complexLieAlgebra A →
    IsBondForm complexLieAlgebra A' →
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), A b = A' b) →
      linearizedConstraint V A c = linearizedConstraint V A' c
  eventually_constraintMapDefined : ∀ B : BondAtLevel L m K k → ComplexMatrix2,
    IsBondForm complexLieAlgebra B →
    ∀ᶠ t in 𝓝 (0 : ℂ), ConstraintMapDefined V (t • B) c
  hasDerivAt_constraintMap : ∀ B : BondAtLevel L m K k → ComplexMatrix2,
    IsBondForm complexLieAlgebra B →
    HasDerivAt (fun t : ℂ => constraintMap V (t • B) c)
      ((L : ℂ) • linearizedConstraint V B c) 0
def LinearizedConstraintAtBond.Statement : Prop :=
  ∀ (L m K k : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (V : BondAtLevel L m K k → ComplexMatrix2) (c : BondAtLevel L m K (k + 1)),
      c.IsPositivelyOriented →
      V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) →
      LinearizedConstraintProperties V c
end PeriodicLattice
end YangMills.Construction
