import YangMills.Construction.Lattice.TowersAndStepSetsCarriedByIsometries
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ParameterChoice YangMills.Construction.Conventions
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def IsometriesPreserveTowersAndStepCubes : Prop :=
  (∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m), IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i →
      PreservesTowers i σ ∧ PreservesDeterminingSets i σ ∧
      PreservesActiveSets i σ ∧ PreservesMinimalSets i σ ∧
      PreservesGluing i σ ∧ PreservesMultiShellGluing i σ) ∧
  ∀ (c : ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ) (i : ℤ)
    (σ : FourTorus c.L m ≃ FourTorus c.L m), IsAdmissibleBlockingFactor c.L → 0 < m → -(m : ℤ) ≤ i →
    σ ∈ latticeIsometries c.L m i →
      CubesOfStep.PreservesStepPartitions c K x i σ ∧ CubesOfStep.PreservesStepSets c K x i σ
end YangMills.Construction.PeriodicLattice
