import YangMills.Construction.Continuum.ConfigurationSpace
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
def MinSeparationLipschitz (n : ℕ) : Prop :=
  (∀ x : Config n, minSeparation x ≠ ⊤) ∧
  (∀ x x' : Config n,
    |(minSeparation x).toReal - (minSeparation x').toReal| ≤ 2 * configMaxNorm (x - x')) ∧
  Continuous fun x : Config n => (minSeparation x).toReal
def FatDiagonalEqZeros (n : ℕ) : Prop :=
  fatDiagonal n = {x | minSeparation x = 0} ∧ IsClosed (fatDiagonal n)
def FatDiagonalComplEqInjective (n : ℕ) : Prop :=
  (fatDiagonal n)ᶜ = TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧
  IsOpen (TestFunctions.injectiveTuples (Fin 4 → ℝ) n)
def MinSeparationProperties : Prop :=
  (∀ n : ℕ, 2 ≤ n →
    MinSeparationLipschitz n ∧ FatDiagonalEqZeros n ∧ FatDiagonalComplEqInjective n) ∧
  FatDiagonalEqZeros 1 ∧ FatDiagonalComplEqInjective 1
end YangMills.Construction.ConfigurationSpace
end
