import YangMills.Construction.Lattice.TowersAndStepSetsCarriedByIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice
def StepCubesAndSetsIsometryInvariant : Prop :=
  ∀ (c : ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ) (i : ℤ)
    (σ : FourTorus c.L m ≃ FourTorus c.L m), Conventions.IsAdmissibleBlockingFactor c.L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries c.L m i →
      CubesOfStep.PreservesStepPartitions c K x i σ ∧ CubesOfStep.PreservesStepSets c K x i σ
end PeriodicLattice
end YangMills.Construction
